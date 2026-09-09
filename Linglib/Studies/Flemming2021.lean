import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Linglib.Phonology.HarmonicGrammar.Noise
import Linglib.Core.Probability.Choice.GumbelLuce
import Linglib.Data.Examples.Flemming2021

/-!
# Flemming (2021): Comparing MaxEnt and Noisy Harmonic Grammar

This file formalizes [flemming-2021]'s comparison of the stochastic Harmonic Grammars as random
utility models ([train-2009]): noise added to candidate harmonies, Gumbel for MaxEnt
([goldwater-johnson-2003], [hayes-wilson-2008]), normal on the constraint weights for Noisy
Harmonic Grammar ([boersma-pater-2016]), normal on the candidates for normal MaxEnt
([hayes-2017]). Between two candidates the probability of the first is `F_d` of the harmony
difference (7), so its logit is the harmony difference in MaxEnt (10) and its probit the harmony
difference divided by the noise standard deviation `σ_d` in the normal models (16), (18) — a
constant `ε√2` for normal MaxEnt but, for NHG, `σ` times the root of the summed squared violation
differences (14). Hence adding a constraint violation always changes the MaxEnt logit by the
constraint's weight (§7.1, `hDiff_following`), while the NHG probit change depends on the
harmony difference before the change (38), (`nhgProbitChange_strictAnti`).

The test case is [smith-pater-2020]'s French schwa data (19): eight contexts crossing an
underlying schwa or none, a preceding C or CC, and a following monosyllable or disyllable,
evaluated by NoSchwa, \*CCC, \*Clash, Max, Dep and \*Cluster (20)–(28). The difference tableau
(35) is derived from those definitions (`diff_eq`), the three MaxEnt uniformity predictions and
the NHG ordering of probit gains 1-2 > 5-6 > 3-4 > 7-8 follow (`logit_following`,
`clash_gain_ordered`), and the observed rates of Table 2 show the interaction between Max and
\*CCC that the revised constraint \*CCC/iP of §8.3 accounts for (`onset_effect_larger_for_words`,
`hDiffRevised_onset`). Tableau (45) closes with the three-candidate case where NHG separates two
equal-harmony candidates by their noise covariance (§9).

## Implementation notes

* Candidates are `Fin 2`, `0` the schwa candidate and `1` the schwaless one, so that the
  substrate's `Real.logit_softmax_fin_two` is (10) directly; constraints are `Constraint.binary`
  predicates on the context's three features.
* The fitted weights of Tables 1 and 4 and the deviances of §8 are estimation results and are
  not formalized; the predictions are stated for arbitrary weights with the sign hypotheses the
  fits satisfy. Censored NHG (§7.3) has no closed form and is not formalized.
* The observed rates are hundredths in `Data/Examples/Flemming2021.json`, read by `pObs`; the
  interaction is stated on odds ratios, the exponential of the logit differences MaxEnt predicts
  equal.

## References

* [flemming-2021]
* [smith-pater-2020]
* [boersma-pater-2016]
* [goldwater-johnson-2003]
* [hayes-wilson-2008]
* [hayes-2017]
* [train-2009]
* [mcfadden-1974]
-/

namespace Flemming2021

open Core Real Constraints HarmonicGrammar Data.Examples

/-! ### Stochastic Harmonic Grammars as random utility models (§§4–5) -/

variable {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}

/-- MaxEnt is the Gumbel random utility model (§4): the probability of the highest harmony under
i.i.d. Gumbel noise is the softmax of (4), by Lemma 1 of [mcfadden-1974]. -/
theorem maxent_eq_gumbelRUM [DecidableEq C] (con : CON C n) (w : Fin n → ℝ) (c : C) :
    rumMaxProb (gumbelPDFReal 0 1) (λ x => ProbabilityTheory.cdf (gumbelMeasure 0 1) x)
      (harmonyScore con w) c = softmax (harmonyScore con w) c := by
  rw [rumMaxProb_gumbel_eq_softmax _ one_pos c]
  norm_num [one_smul]

/-- (10): between two candidates, the MaxEnt logit of the first is the harmony difference. -/
theorem logit_maxent (con : CON (Fin 2) n) (w : Fin n → ℝ) :
    logit (softmax (harmonyScore con w) 0) = harmonyScore con w 0 - harmonyScore con w 1 :=
  logit_softmax_fin_two _

omit [Fintype C] [Nonempty C] in
/-- (16): the NHG probit of the first candidate is the harmony difference over `σ_d`. -/
theorem probit_nhg (con : CON C n) (w : Fin n → ℝ) (σ : ℝ) (a b : C) :
    probit (nhgChoiceProb con w σ a b) =
      (harmonyScore con w a - harmonyScore con w b) / nhgSigmaD con σ a b := by
  rw [nhg_choiceProb_eq, probit_normalCDF]

omit [Fintype C] [Nonempty C] in
/-- (18): the normal MaxEnt probit is the harmony difference over the constant `ε√2`. -/
theorem probit_normalMaxEnt (con : CON C n) (w : Fin n → ℝ) (ε : ℝ) (a b : C) :
    probit (normalMaxEntChoiceProb con w ε a b) =
      (harmonyScore con w a - harmonyScore con w b) / normalMaxEntSigmaD ε := by
  rw [normalMaxEnt_choiceProb_eq, probit_normalCDF]

/-! ### The effect of a change in violations on the NHG probit (§7.2) -/

/-- (38a): the change in the NHG probit when the harmony difference `h` changes by `Δh` and the
noise standard deviation from `σ` to `σ'`. -/
noncomputable def nhgProbitChange (h Δh σ σ' : ℝ) : ℝ := (h + Δh) / σ' - h / σ

/-- (38b): the change decomposes into a term proportional to the initial harmony difference and
the rescaled harmony change. -/
theorem nhgProbitChange_eq (h Δh : ℝ) {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ') :
    nhgProbitChange h Δh σ σ' = h * (σ - σ') / (σ * σ') + Δh / σ' := by
  unfold nhgProbitChange
  field_simp
  ring

/-- When the change enlarges the noise, `σ < σ'`, the probit gain decreases with the initial
harmony difference: the same change in violations has a smaller effect the higher the schwa
candidate already stands (§7.2). -/
theorem nhgProbitChange_strictAnti (Δh : ℝ) {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : σ < σ') :
    StrictAnti (nhgProbitChange · Δh σ σ') := by
  intro h₁ h₂ hlt
  have hσ'0 : 0 < σ' := hσ.trans hσ'
  have key : nhgProbitChange h₂ Δh σ σ' - nhgProbitChange h₁ Δh σ σ' =
      (h₂ - h₁) * (1 / σ' - 1 / σ) := by
    unfold nhgProbitChange
    field_simp
    ring
  have hneg : 1 / σ' - 1 / σ < 0 := sub_neg.2 (one_div_lt_one_div_of_lt hσ hσ')
  have := mul_neg_of_pos_of_neg (sub_pos.2 hlt) hneg
  linarith

/-! ### French schwa (§6): the contexts of (19) and the constraints of (20)–(23) -/

/-- Whether the schwa site is clitic-final, with an underlying schwa, or word-final, with none. -/
inductive Underlying where
  | schwa
  | zero
  deriving DecidableEq, Repr, Fintype

/-- Whether one or two consonants precede the schwa site. -/
inductive Onset where
  | c
  | cc
  deriving DecidableEq, Repr, Fintype

/-- Whether the following word is a stressed monosyllable (`–ś`) or a disyllable (`–sś`). -/
inductive Following where
  | monosyllable
  | disyllable
  deriving DecidableEq, Repr, Fintype

/-- A context of (19). -/
structure Context where
  underlying : Underlying
  onset : Onset
  following : Following
  deriving DecidableEq, Repr

/-- The two candidates of each tableau: `0` realizes the schwa, `1` does not. -/
abbrev Cand := Fin 2

/-- (20) NoSchwa: one violation for the schwa in the output. -/
def noSchwa (_ : Context) : Constraint Cand := .binary (· = 0)

/-- (21) \*CCC: the schwaless candidate after two consonants forms a three-consonant cluster. -/
def starCCC (x : Context) : Constraint Cand := .binary λ c => c = 1 ∧ x.onset = .cc

/-- (23) \*Clash: without the schwa, a stressed monosyllable follows a stressed syllable. -/
def starClash (x : Context) : Constraint Cand := .binary λ c => c = 1 ∧ x.following = .monosyllable

/-- Max: the schwaless candidate deletes an underlying schwa. -/
def maxSchwa (x : Context) : Constraint Cand := .binary λ c => c = 1 ∧ x.underlying = .schwa

/-- Dep: the schwa candidate inserts a schwa where there is none underlyingly. -/
def depSchwa (x : Context) : Constraint Cand := .binary λ c => c = 0 ∧ x.underlying = .zero

/-- (22) \*Cluster: a two-consonant cluster, in the schwaless candidate always and in the schwa
candidate after two consonants. -/
def starCluster (x : Context) : Constraint Cand := .binary λ c => c = 1 ∨ x.onset = .cc

/-- [smith-pater-2020]'s constraint set in the order of (35). -/
def constraints (x : Context) : CON Cand 6
  | 0 => noSchwa x
  | 1 => starCCC x
  | 2 => starClash x
  | 3 => maxSchwa x
  | 4 => depSchwa x
  | 5 => starCluster x

/-- The difference tableau: the schwa candidate's violations minus the schwaless candidate's,
signed as the paper signs violations (negative). -/
def diff (x : Context) (k : Fin 6) : ℤ := (constraints x k 1 : ℤ) - constraints x k 0

/-- The difference tableaux of (35), derived from the constraint definitions. -/
theorem diff_eq : ∀ u o f, List.ofFn (diff ⟨u, o, f⟩) =
    match u, o, f with
    | .zero, .c, .disyllable => [-1, 0, 0, 0, -1, 1]
    | .zero, .c, .monosyllable => [-1, 0, 1, 0, -1, 1]
    | .zero, .cc, .disyllable => [-1, 1, 0, 0, -1, 0]
    | .zero, .cc, .monosyllable => [-1, 1, 1, 0, -1, 0]
    | .schwa, .c, .disyllable => [-1, 0, 0, 1, 0, 1]
    | .schwa, .c, .monosyllable => [-1, 0, 1, 1, 0, 1]
    | .schwa, .cc, .disyllable => [-1, 1, 0, 1, 0, 0]
    | .schwa, .cc, .monosyllable => [-1, 1, 1, 1, 0, 0] := by
  decide

/-- `hə − h∅`, the harmony difference of a context under weights `w`. -/
noncomputable def hDiff (x : Context) (w : Fin 6 → ℝ) : ℝ :=
  harmonyScore (constraints x) w 0 - harmonyScore (constraints x) w 1

/-- The harmony difference is the weighted difference tableau, as in (29)–(34). -/
theorem hDiff_eq_sum (x : Context) (w : Fin 6 → ℝ) : hDiff x w = ∑ k, w k * diff x k := by
  simp only [hDiff, harmonyScore_diff, diff, Int.cast_sub, Int.cast_natCast, mul_sub,
    Finset.sum_sub_distrib]
  ring

private theorem hDiff_closed (u : Underlying) (o : Onset) (f : Following) (w : Fin 6 → ℝ) :
    hDiff ⟨u, o, f⟩ w = -w 0 + (if o = .cc then w 1 else 0) + (if f = .monosyllable then w 2 else 0)
      + (if u = .schwa then w 3 else 0) - (if u = .zero then w 4 else 0)
      + (if o = .c then w 5 else 0) := by
  rw [hDiff_eq_sum, Fin.sum_univ_six]
  cases u <;> cases o <;> cases f <;>
    simp [diff, constraints, noSchwa, starCCC, starClash, maxSchwa, depSchwa, starCluster] <;> ring

/-! ### MaxEnt predicts uniform logit differences (§7.1) -/

/-- Adding the \*Clash violation, `–sś` to `–ś`, raises the harmony difference by the weight of
\*Clash whatever the other features. -/
theorem hDiff_following (u : Underlying) (o : Onset) (w : Fin 6 → ℝ) :
    hDiff ⟨u, o, .monosyllable⟩ w - hDiff ⟨u, o, .disyllable⟩ w = w 2 := by
  rw [hDiff_closed, hDiff_closed]; simp

/-- Two preceding consonants add a \*CCC and remove a \*Cluster violation difference. -/
theorem hDiff_onset (u : Underlying) (f : Following) (w : Fin 6 → ℝ) :
    hDiff ⟨u, .cc, f⟩ w - hDiff ⟨u, .c, f⟩ w = w 1 - w 5 := by
  rw [hDiff_closed, hDiff_closed]; simp; ring

/-- An underlying schwa adds a Max and removes a Dep violation difference. -/
theorem hDiff_underlying (o : Onset) (f : Following) (w : Fin 6 → ℝ) :
    hDiff ⟨.schwa, o, f⟩ w - hDiff ⟨.zero, o, f⟩ w = w 3 + w 4 := by
  rw [hDiff_closed, hDiff_closed]; simp

/-- The MaxEnt probability of the schwa candidate. -/
noncomputable def pMaxEnt (x : Context) (w : Fin 6 → ℝ) : ℝ :=
  softmax (harmonyScore (constraints x) w) 0

theorem logit_pMaxEnt (x : Context) (w : Fin 6 → ℝ) : logit (pMaxEnt x w) = hDiff x w :=
  logit_softmax_fin_two _

/-- MaxEnt predicts the same logit difference, the weight of \*Clash, across the four pairs
1-2, 3-4, 5-6, 7-8. -/
theorem logit_following (u : Underlying) (o : Onset) (w : Fin 6 → ℝ) :
    logit (pMaxEnt ⟨u, o, .monosyllable⟩ w) - logit (pMaxEnt ⟨u, o, .disyllable⟩ w) = w 2 := by
  rw [logit_pMaxEnt, logit_pMaxEnt, hDiff_following]

/-- … and the same logit difference across the pairs 1-3, 2-4, 5-7, 6-8. -/
theorem logit_onset (u : Underlying) (f : Following) (w : Fin 6 → ℝ) :
    logit (pMaxEnt ⟨u, .cc, f⟩ w) - logit (pMaxEnt ⟨u, .c, f⟩ w) = w 1 - w 5 := by
  rw [logit_pMaxEnt, logit_pMaxEnt, hDiff_onset]

/-- … and across the pairs 1-5, 2-6, 3-7, 4-8. -/
theorem logit_underlying (o : Onset) (f : Following) (w : Fin 6 → ℝ) :
    logit (pMaxEnt ⟨.schwa, o, f⟩ w) - logit (pMaxEnt ⟨.zero, o, f⟩ w) = w 3 + w 4 := by
  rw [logit_pMaxEnt, logit_pMaxEnt, hDiff_underlying]

/-! ### NHG predicts context-dependent probit differences (§7.2, §8.2) -/

/-- The NHG probability of the schwa candidate with weight noise `σ`. -/
noncomputable def pNHG (x : Context) (w : Fin 6 → ℝ) (σ : ℝ) : ℝ :=
  nhgChoiceProb (constraints x) w σ 0 1

/-- The summed squared violation differences (37): the number of differing constraints, 4 with
the \*Clash difference and 3 without (Table 3). -/
theorem violationDiffSqSum_eq (x : Context) :
    violationDiffSqSum (constraints x) 0 1 = if x.following = .monosyllable then 4 else 3 := by
  obtain ⟨u, o, f⟩ := x
  rw [violationDiffSqSum, Fin.sum_univ_six]
  cases u <;> cases o <;> cases f <;>
    simp [constraints, noSchwa, starCCC, starClash, maxSchwa, depSchwa, starCluster] <;> norm_num

/-- (36): the NHG probit of the schwa candidate. -/
theorem probit_pNHG (x : Context) (w : Fin 6 → ℝ) (σ : ℝ) :
    probit (pNHG x w σ) =
      hDiff x w / (σ * √(if x.following = .monosyllable then 4 else 3)) := by
  rw [pNHG, probit_nhg, nhgSigmaD, violationDiffSqSum_eq]
  rfl

/-- The probit gain from the \*Clash violation is (38a) with `Δh` the weight of \*Clash, `σ_d = σ√3`
and `σ_d' = 2σ`. -/
theorem probit_gain_following (u : Underlying) (o : Onset) (w : Fin 6 → ℝ) (σ : ℝ) :
    probit (pNHG ⟨u, o, .monosyllable⟩ w σ) - probit (pNHG ⟨u, o, .disyllable⟩ w σ) =
      nhgProbitChange (hDiff ⟨u, o, .disyllable⟩ w) (w 2) (σ * √3) (2 * σ) := by
  rw [probit_pNHG, probit_pNHG, nhgProbitChange, ← hDiff_following u o w]
  simp only [if_true, if_false, reduceCtorEq]
  rw [show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

/-- §8.2: with positive weights and the Max and Dep effect below the \*CCC one, the initial harmony
differences of the four \*Clash pairs are ordered 1 < 5 < 3 < 7, so NHG predicts their probit
gains ordered 1-2 > 5-6 > 3-4 > 7-8 — where the data show the same gain in three of the four. -/
theorem clash_gain_ordered (w : Fin 6 → ℝ) {σ : ℝ} (hσ : 0 < σ) (hw : 0 < w 3 + w 4)
    (hw' : w 3 + w 4 < w 1 - w 5) :
    let gain u o := probit (pNHG ⟨u, o, .monosyllable⟩ w σ) - probit (pNHG ⟨u, o, .disyllable⟩ w σ)
    gain .schwa .c < gain .zero .c ∧ gain .zero .cc < gain .schwa .c ∧
      gain .schwa .cc < gain .zero .cc := by
  intro gain
  have hanti := nhgProbitChange_strictAnti (w 2) (mul_pos hσ (Real.sqrt_pos.2 (by norm_num)))
    (show σ * √3 < 2 * σ by
      rw [mul_comm]
      exact mul_lt_mul_of_pos_right (Real.sqrt_lt' (by norm_num) |>.2 (by norm_num)) hσ)
  have h15 := hDiff_underlying .c .disyllable w
  have h13 := hDiff_onset .zero .disyllable w
  have h37 := hDiff_underlying .cc .disyllable w
  simp only [gain, probit_gain_following]
  exact ⟨hanti (by linarith), hanti (by linarith), hanti (by linarith)⟩

/-- For the pairs differing in the preceding consonants, `σ_d` is unchanged, so the NHG probit gain
is the rescaled harmony change (41): the same for words and clitics, larger before a monosyllable
than before a disyllable. -/
theorem probit_gain_onset (u : Underlying) (f : Following) (w : Fin 6 → ℝ) (σ : ℝ) :
    probit (pNHG ⟨u, .cc, f⟩ w σ) - probit (pNHG ⟨u, .c, f⟩ w σ) =
      (w 1 - w 5) / (σ * √(if f = .monosyllable then 4 else 3)) := by
  rw [probit_pNHG, probit_pNHG, ← sub_div, hDiff_onset]

/-! ### The observed rates (Table 2) and the revised constraint set (§8.3) -/

/-- A context with the observed probability of pronouncing the schwa, in hundredths. -/
structure Row where
  ctx : Context
  pSchwa : ℕ
  deriving DecidableEq, Repr

def underlyingTable : List (String × Underlying) := [("schwa", .schwa), ("zero", .zero)]

def onsetTable : List (String × Onset) := [("C", .c), ("CC", .cc)]

def followingTable : List (String × Following) :=
  [("monosyllable", .monosyllable), ("disyllable", .disyllable)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let u ← ex.parse? "underlying" underlyingTable
  let o ← ex.parse? "onset" onsetTable
  let f ← ex.parse? "following" followingTable
  let p ← ex.nat? "pSchwa"
  pure ⟨⟨u, o, f⟩, p⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The observed rate of a context, in hundredths. -/
def pObs (x : Context) : ℕ := ((rows.find? (·.ctx = x)).map Row.pSchwa).getD 0

theorem rows_cover : ∀ u o f, (rows.find? (·.ctx = ⟨u, o, f⟩)).isSome := by decide

/-- The schwa is pronounced more often before a monosyllable in every pair, as every model with a
positive \*Clash weight predicts. -/
theorem pObs_following : ∀ u o, pObs ⟨u, o, .disyllable⟩ < pObs ⟨u, o, .monosyllable⟩ := by
  decide

/-- MaxEnt's side of that prediction: a positive \*Clash weight raises the schwa's probability. -/
theorem pMaxEnt_following_lt (u : Underlying) (o : Onset) (w : Fin 6 → ℝ) (hw : 0 < w 2) :
    pMaxEnt ⟨u, o, .disyllable⟩ w < pMaxEnt ⟨u, o, .monosyllable⟩ w := by
  simp only [pMaxEnt, softmax_fin_two]
  exact sigmoid_strictMono (by have := hDiff_following u o w; unfold hDiff at this; linarith)

/-- The observed odds of the schwa. -/
def odds (x : Context) : ℚ := pObs x / (100 - pObs x)

/-- §8.2: the effect of the preceding consonants is larger in words than in clitics — the odds ratio
across \*CCC is larger with underlying `/∅/` than with `/ə/`, in both stress contexts. MaxEnt with
Smith & Pater's constraints predicts equal odds ratios (`logit_onset`); this is the Max × \*CCC
interaction that motivates \*CCC/iP. -/
theorem onset_effect_larger_for_words : ∀ f,
    odds ⟨.schwa, .cc, f⟩ / odds ⟨.schwa, .c, f⟩ < odds ⟨.zero, .cc, f⟩ / odds ⟨.zero, .c, f⟩ := by
  have h : ∀ u o f, pObs ⟨u, o, f⟩ = match u, o, f with
      | .zero, .c, .disyllable => 9 | .zero, .c, .monosyllable => 12
      | .zero, .cc, .disyllable => 68 | .zero, .cc, .monosyllable => 83
      | .schwa, .c, .disyllable => 56 | .schwa, .c, .monosyllable => 65
      | .schwa, .cc, .disyllable => 91 | .schwa, .cc, .monosyllable => 94 := by decide
  intro f
  cases f <;> simp only [odds, h] <;> norm_num

/-- \*CCC/iP (§8.3): a three-consonant cluster within one intermediate phrase, which the
schwaless candidate forms after two consonants only in the word-final items. -/
def starCCCiP (x : Context) : Constraint Cand :=
  .binary λ c => c = 1 ∧ x.onset = .cc ∧ x.underlying = .zero

/-- Max and Dep collapsed into one correspondence constraint (§8.3). -/
def corr (x : Context) : Constraint Cand :=
  .binary λ c => (c = 1 ∧ x.underlying = .schwa) ∨ (c = 0 ∧ x.underlying = .zero)

/-- The revised constraint set of Table 4: NoSchwa, \*CCC, \*CCC/iP, \*Clash, Max/Dep, \*Cluster. -/
def revised (x : Context) : CON Cand 6
  | 0 => noSchwa x
  | 1 => starCCC x
  | 2 => starCCCiP x
  | 3 => starClash x
  | 4 => corr x
  | 5 => starCluster x

/-- `hə − h∅` under the revised constraint set. -/
noncomputable def hDiffRevised (x : Context) (w : Fin 6 → ℝ) : ℝ :=
  harmonyScore (revised x) w 0 - harmonyScore (revised x) w 1

/-- With \*CCC/iP the effect of the preceding consonants on the harmony difference is larger in
words by the weight of \*CCC/iP, so a MaxEnt grammar can fit the interaction (§8.3). -/
theorem hDiffRevised_onset (u : Underlying) (f : Following) (w : Fin 6 → ℝ) :
    hDiffRevised ⟨u, .cc, f⟩ w - hDiffRevised ⟨u, .c, f⟩ w =
      w 1 - w 5 + if u = .zero then w 2 else 0 := by
  simp only [hDiffRevised, harmonyScore_diff, Fin.sum_univ_six]
  cases u <;> cases f <;>
    simp [revised, noSchwa, starCCC, starCCCiP, starClash, corr, starCluster] <;> ring

/-! ### Three candidates (§9): tableau (45) -/

/-- The tableau of (1), (3), (5) and (45): candidates `a`, `b`, `c` as `0`, `1`, `2`. -/
def tableCon : CON (Fin 3) 3
  | 0 => λ c => if c = 0 then 1 else 0
  | 1 => λ c => if c = 1 then 2 else if c = 2 then 1 else 0
  | 2 => λ c => if c = 2 then 1 else 0

/-- The weights 15, 8, 8. -/
noncomputable def tableW : Fin 3 → ℝ
  | 0 => 15
  | 1 => 8
  | 2 => 8

/-- Candidates `b` and `c` have equal harmony, `−16`. -/
theorem table45_harmony :
    harmonyScore tableCon tableW 0 = -15 ∧ harmonyScore tableCon tableW 1 = -16 ∧
      harmonyScore tableCon tableW 2 = -16 := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_three, tableCon, tableW]; norm_num

/-- (5): MaxEnt gives `a` the probability `e⁻¹⁵ / (e⁻¹⁵ + 2e⁻¹⁶) = 1 / (1 + 2e⁻¹)`, 0.58, and
`b` and `c` equal probabilities. -/
theorem table45_maxent :
    softmax (harmonyScore tableCon tableW) 0 = 1 / (1 + 2 * exp (-1)) ∧
      softmax (harmonyScore tableCon tableW) 1 = softmax (harmonyScore tableCon tableW) 2 := by
  obtain ⟨h0, h1, h2⟩ := table45_harmony
  refine ⟨?_, by simp only [softmax, h1, h2]⟩
  simp only [softmax, Fin.sum_univ_three, h0, h1, h2]
  rw [show (-16 : ℝ) = -15 + -1 by norm_num, exp_add]
  field_simp
  ring

/-- §9: in NHG the noise differences relative to `b` have variances 5 and 2 (14) and covariance 2,
so the joint distribution is not determined by the harmony differences and `b` and `c` receive
different probabilities despite equal harmony. -/
theorem table45_nhg :
    violationDiffSqSumQ tableCon 0 1 = 5 ∧ violationDiffSqSumQ tableCon 2 1 = 2 ∧
      nhgCovarianceQ tableCon 1 0 2 = 2 := by
  simp [violationDiffSqSumQ, nhgCovarianceQ, Fin.sum_univ_three, tableCon]; norm_num

end Flemming2021
