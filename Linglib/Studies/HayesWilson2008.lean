import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Linglib.Core.Optimization.System
import Linglib.Core.Probability.SoftmaxTheory
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.Segmental.Defs
import Linglib.Data.Examples.HayesWilson2008

/-!
# Hayes and Wilson (2008): A Maximum Entropy Model of Phonotactics and Phonotactic Learning

This file formalizes the maxent phonotactic grammar of [hayes-wilson-2008]: a constraint is a
sequence of feature matrices, one of which may be complemented (§4.1.1), and a grammar assigns
each form the score (4), the maxent value (5), and the probability (6). The weights are learned
by maximizing the probability of the data (7), whose partial derivatives are the differences
between expected (8) and observed violation counts: `hasDerivAt_logLik`. The grammar the
learner found for English onsets (Table 4) is stated over the paper's feature chart (Table 3),
and every score §5.2–5.3 report is recomputed from it: `attested_penalized` finds exactly the
ten attested onsets the grammar penalizes, `twelve_scores` and `h_rt` reproduce the unattested
scores, and the gangs of §5.2 decompose into their members. The predicted rating (12) orders
forms as the score does (`rating_lt_iff`), so the reported correlation with Scholes's ratings is
a claim about the score alone.

## Implementation notes

Weights are kept in hundredths over `ℕ`, so every score is computed by `decide`; the maxent
value and probability then live over `ℝ`. Scores computed from the two-decimal weights of
Table 4 can differ from the paper's reported values by one hundredth ([ð] 4.53 here against
4.54; [θw] 3.90 against 3.91; [θ] and [θr] 1.84 against 1.85): `rows_scores` states the
reproduction to within that rounding. Complement matrices are read against the
underspecified chart, so `[^+back]` contains every consonant unspecified for backness, as
#15 requires. The probability (6) over the infinite set of forms is realized on a finite
candidate set through `ConstraintSystem` with `softmaxDecoder 1`, and the learning objective
over a finite form space; the paper's finite-state approximation of the expected counts is not
modelled. The ratings of Scholes's experiment appear only as a scattergram (Figure 3), so the
correlation of 0.946 and Table 5 stay in prose.

## TODO

* The constraint search of §4 (accuracy O/E with the upper confidence limit, generality, the
  algorithm (10)) and the Gaussian prior of footnote 4.
* Projections (§6–§7), the Shona and stress simulations, and Wargamay (§8).

## References

* [hayes-wilson-2008]
* [della-pietra-della-pietra-lafferty-1997]
* [scholes-1966]
* [clements-keyser-1983]
* [goldwater-johnson-2003]
-/

namespace HayesWilson2008

open Data.Examples Phonology Constraints Real

/-! ### The segments of Table 3 -/

/-- The English consonants of Table 3; the segments without an ASCII letter are named as in
    ARPAbet: `ch` [tʃ], `jh` [dʒ], `th` [θ], `sh` [ʃ], `hh` [h], `dh` [ð],
    `zh` [ʒ], `ng` [ŋ]. -/
inductive Seg
  | p | t | ch | k | b | d | jh | g | f | th | s | sh | hh | v | dh | z | zh | m | n | ng | l | r
  | j | w
  deriving DecidableEq, Repr

namespace Seg

/-- Table 3, one row per feature: the segments specified `+`, then those specified `−`; a
    segment in neither list is unspecified for the feature, the chart's blanks (privative and
    contrastive underspecification, §4.1.2). -/
def chart : Feature → List Seg × List Seg
  | .consonantal =>
    ([p, t, ch, k, b, d, jh, g, f, th, s, sh, hh, v, dh, z, zh, m, n, ng, l], [r, j, w])
  | .approximant =>
    ([l, r, j, w], [p, t, ch, k, b, d, jh, g, f, th, s, sh, hh, v, dh, z, zh, m, n, ng])
  | .sonorant =>
    ([m, n, ng, l, r, j, w], [p, t, ch, k, b, d, jh, g, f, th, s, sh, hh, v, dh, z, zh])
  | .continuant => ([f, th, s, sh, hh, v, dh, z, zh], [p, t, ch, k, b, d, jh, g])
  | .nasal => ([m, n, ng], [])
  | .voice => ([b, d, jh, g, v, dh, z, zh], [p, t, ch, k, f, th, s, sh, hh])
  | .spreadGlottis => ([hh], [])
  | .labial => ([p, b, f, v, m, w], [])
  | .coronal => ([t, ch, d, jh, th, s, sh, dh, z, zh, n, l, r], [])
  | .anterior => ([t, d, th, s, dh, z, n, l], [ch, jh, sh, zh, r])
  | .strident => ([ch, jh, s, sh, z, zh], [t, d, th, dh, n, l, r])
  | .lateral => ([l], [])
  | .dorsal => ([k, g, ng], [])
  | .high => ([j, w], [])
  | .back => ([w], [j])
  | _ => ([], [])

/-- The feature specification of a segment, read off the chart. -/
def spec (x : Seg) : Segment := λ f =>
  if x ∈ (chart f).1 then Flat.some true else if x ∈ (chart f).2 then Flat.some false else ⊥

/-- The segment written by one IPA letter. -/
def ofChar : Char → Option Seg
  | 'p' => some p | 't' => some t | 'k' => some k | 'b' => some b | 'd' => some d
  | 'g' => some g | 'f' => some f | 'θ' => some th | 's' => some s | 'ʃ' => some sh
  | 'h' => some hh | 'v' => some v | 'ð' => some dh | 'z' => some z | 'ʒ' => some zh
  | 'm' => some m | 'n' => some n | 'ŋ' => some ng | 'l' => some l | 'r' => some r
  | 'j' => some j | 'w' => some w | _ => none

/-- Read an onset off a row's IPA string; the affricates are written as digraphs. -/
def parse : List Char → Option (List Seg)
  | [] => some []
  | 't' :: 'ʃ' :: cs => (parse cs).map (ch :: ·)
  | 'd' :: 'ʒ' :: cs => (parse cs).map (jh :: ·)
  | c :: cs => (ofChar c).bind λ x => (parse cs).map (x :: ·)

end Seg

/-! ### Constraints (§4.1.1) -/

/-- A matrix of a constraint ((9)): a natural class `[αF, βG, …]`, its complement
    `[^αF, βG, …]` (the implication operator), or the word boundary `#`. -/
inductive Matrix
  | cls (pat : Segment)
  | compl (pat : Segment)
  | boundary

variable {α : Type*}

/-- A matrix matches one symbol of a boundary-padded form, read through the segment
    specification `spec`; `none` is a word boundary. -/
def Matrix.Matches (spec : α → Segment) : Matrix → Option α → Prop
  | .cls pat, some x => pat ≤ spec x
  | .compl pat, some x => ¬ pat ≤ spec x
  | .boundary, none => True
  | _, _ => False

instance (spec : α → Segment) : ∀ (m : Matrix) (x : Option α), Decidable (m.Matches spec x)
  | .cls _, some _ => inferInstanceAs (Decidable (_ ≤ _))
  | .compl _, some _ => inferInstanceAs (Decidable (¬ _ ≤ _))
  | .boundary, none => inferInstanceAs (Decidable True)
  | .cls _, none | .compl _, none | .boundary, some _ => inferInstanceAs (Decidable False)

/-- A phonotactic constraint ((9)): a sequence of matrices. -/
abbrev Cx := List Matrix

/-- The matrices match the padded form from its first symbol on. -/
def Cx.prefixMatch (spec : α → Segment) : Cx → List (Option α) → Bool
  | [], _ => true
  | m :: ms, x :: xs => decide (m.Matches spec x) && Cx.prefixMatch spec ms xs
  | _ :: _, [] => false

/-- The violations of a constraint on a form: the positions of the boundary-padded form at
    which the matrices match ((9): the constraint returns the number of matches). -/
def Cx.violations (spec : α → Segment) (c : Cx) (form : List α) : ℕ :=
  ((none :: form.map some ++ [none]).tails.filter (c.prefixMatch spec)).length

/-- The class `[αF, βG, …]`. -/
def M (l : List (Feature × Bool)) : Matrix := .cls (Segment.ofSpecs l)

/-- The complement class `[^αF, βG, …]`. -/
def M' (l : List (Feature × Bool)) : Matrix := .compl (Segment.ofSpecs l)

/-- `[ ]`: any segment. -/
def any : Matrix := .cls (Segment.ofSpecs [])

/-! ### Score, maxent value, and probability (§3.2) -/

/-- The score (4) of a form under a grammar with weights in hundredths. -/
def score {n : ℕ} (spec : α → Segment) (con : Fin n → Cx) (w : Fin n → ℕ)
    (form : List α) : ℕ :=
  weightedViolations w λ j => (con j).violations spec form

/-- The maxent value (5), `exp (−h(x))`, of a form whose score in hundredths is `k`. -/
noncomputable def maxentValue (k : ℕ) : ℝ := exp (-(k : ℝ) / 100)

theorem maxentValue_pos (k : ℕ) : 0 < maxentValue k := exp_pos _

/-- Forms with more violations get lower values. -/
theorem maxentValue_lt_iff {k₁ k₂ : ℕ} :
    maxentValue k₁ < maxentValue k₂ ↔ k₂ < k₁ := by
  rw [maxentValue, maxentValue, exp_lt_exp, div_lt_div_iff_of_pos_right (by norm_num),
    neg_lt_neg_iff, Nat.cast_lt]

/-- A violation-free form has the highest possible maxent value, 1. -/
theorem maxentValue_zero : maxentValue 0 = 1 := by simp [maxentValue]

/-- The predicted rating (12): the maxent value raised to `1 / T` for a temperature `T`. -/
noncomputable def rating (T : ℝ) (k : ℕ) : ℝ := maxentValue k ^ (1 / T)

/-- The rating orders forms exactly as the score does, so a correlation with the ratings is a
    claim about the score. -/
theorem rating_lt_iff {T : ℝ} (hT : 0 < T) {k₁ k₂ : ℕ} :
    rating T k₁ < rating T k₂ ↔ k₂ < k₁ := by
  rw [rating, rating, rpow_lt_rpow_iff (maxentValue_pos _).le (maxentValue_pos _).le
    (one_div_pos.2 hT), maxentValue_lt_iff]

/-- Table 1: two constraints, `*#V` weighted 3.0 and `*C#` weighted 2.0, on schematic forms. -/
inductive CV
  | C
  | V
  deriving DecidableEq, Repr

/-- `C` is `[−syllabic]`, `V` is `[+syllabic]` (footnote 7). -/
def CV.spec : CV → Segment
  | .C => Segment.ofSpecs [(.syllabic, false)]
  | .V => Segment.ofSpecs [(.syllabic, true)]

/-- The constraints of Table 1. -/
def table1 : Fin 2 → Cx :=
  ![[.boundary, M [(.syllabic, true)]], [M [(.syllabic, false)], .boundary]]

/-- The weights of Table 1, in hundredths. -/
def table1W : Fin 2 → ℕ := ![300, 200]

/-- Table 1's scores: `CV` 0, `CVC` 2.0, `V` 3.0. -/
theorem table1_scores :
    score CV.spec table1 table1W [.C, .V] = 0 ∧
      score CV.spec table1 table1W [.C, .V, .C] = 200 ∧
        score CV.spec table1 table1W [.V] = 300 := by decide

/-- Table 1's maxent values: 1, `exp (−2)`, `exp (−3)`. -/
theorem table1_maxentValues :
    maxentValue (score CV.spec table1 table1W [.C, .V]) = 1 ∧
      maxentValue (score CV.spec table1 table1W [.C, .V, .C]) = exp (-2) ∧
        maxentValue (score CV.spec table1 table1W [.V]) = exp (-3) := by
  obtain ⟨h₁, h₂, h₃⟩ := table1_scores
  rw [h₁, h₂, h₃]
  norm_num [maxentValue]

/-! ### Learning the weights (§3.3) -/

/-- Updating one weight splits the weighted sum into that constraint's term and the rest. -/
theorem weightedViolations_update {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (t : ℝ)
    (v : Fin n → ℕ) :
    weightedViolations (Function.update w i t) v =
      t * v i + ∑ j ∈ Finset.univ.erase i, w j * v j := by
  rw [weightedViolations, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), Function.update_self,
    add_comm]
  congr 1
  exact Finset.sum_congr rfl λ j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

section Learning

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {n : ℕ}

/-- The probability (6) of each form of a finite form space under real weights `w`, given the
    violation counts `viol`: the softmax of the negated scores. -/
noncomputable def prob (viol : Fin n → Ω → ℕ) (w : Fin n → ℝ) : Ω → ℝ :=
  softmax λ x => -weightedViolations w λ j => viol j x

/-- The expected number of violations (8) of constraint `i`. -/
noncomputable def expected (viol : Fin n → Ω → ℕ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ x, prob viol w x * viol i x

/-- The observed number of violations of constraint `i` in data given as counts per form. -/
def observed (viol : Fin n → Ω → ℕ) (D : Ω → ℕ) (i : Fin n) : ℕ :=
  ∑ x, D x * viol i x

/-- The log of the probability of the data (7): the forms are independent, so the log
    probabilities add, each weighted by its count. -/
noncomputable def logLik (viol : Fin n → Ω → ℕ) (w : Fin n → ℝ) (D : Ω → ℕ) : ℝ :=
  ∑ x, D x * log (prob viol w x)

/-- The partial derivative of one form's log probability in the weight of constraint `i` is
    the expected count minus the form's own count. -/
theorem hasDerivAt_log_prob (viol : Fin n → Ω → ℕ) (w : Fin n → ℝ) (i : Fin n) (x : Ω) :
    HasDerivAt (λ t => log (prob viol (Function.update w i t) x))
      (expected viol w i - viol i x) (w i) := by
  set s : Ω → ℝ := λ y => -(viol i y : ℝ)
  set r : Ω → ℝ := λ y => -∑ j ∈ Finset.univ.erase i, w j * viol j y
  have hp : ∀ t, prob viol (Function.update w i t) = softmax (t • s + r) := λ t => by
    unfold prob
    congr 1
    funext y
    simp only [weightedViolations_update, Pi.add_apply, Pi.smul_apply, smul_eq_mul, s, r]
    ring
  have hw : prob viol w = softmax ((w i) • s + r) := by
    rw [← hp, Function.update_eq_self]
  have hf : (λ t => log (prob viol (Function.update w i t) x)) =
      λ t => log (softmax (t • s + r) x) := funext λ t => by rw [hp]
  rw [hf]
  convert hasDerivAt_log_softmax s r x (w i) using 1
  simp only [expected, hw, s, mul_neg, Finset.sum_neg_distrib]
  ring

/-- **The gradient of the learning objective** ([della-pietra-della-pietra-lafferty-1997]):
    the partial derivative of the log probability of the data in the weight of constraint `i`
    is its expected count, scaled by the size of the data, minus its observed count; the paper's
    §3.3.2 states the two terms as `O[Cᵢ] − E[Cᵢ]` with the penalty direction in mind. -/
theorem hasDerivAt_logLik (viol : Fin n → Ω → ℕ) (w : Fin n → ℝ) (D : Ω → ℕ)
    (i : Fin n) :
    HasDerivAt (λ t => logLik viol (Function.update w i t) D)
      ((∑ x, D x : ℕ) * expected viol w i - observed viol D i) (w i) := by
  unfold logLik
  refine (HasDerivAt.fun_sum λ x (_ : x ∈ Finset.univ) =>
    (hasDerivAt_log_prob viol w i x).const_mul (D x : ℝ)).congr_deriv ?_
  simp only [observed, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_sub,
    Finset.sum_sub_distrib]

end Learning

/-! ### The learned grammar for English onsets (Table 4) -/

/-- The 23 constraints of Table 4, in the order they were learned. -/
def table4 : Fin 23 → Cx := ![
  [M [(.sonorant, true), (.dorsal, true)]],
  [M [(.continuant, true), (.voice, true), (.anterior, false)]],
  [M' [(.voice, false), (.anterior, true), (.strident, true)], M [(.approximant, false)]],
  [any, M [(.continuant, true)]],
  [any, M [(.voice, true)]],
  [M [(.sonorant, true)], any],
  [M [(.strident, false)], M [(.consonantal, true)]],
  [any, M [(.strident, true)]],
  [M [(.labial, true)], M' [(.approximant, true), (.coronal, true)]],
  [M [(.anterior, false)], M' [(.approximant, true), (.anterior, false)]],
  [M [(.continuant, true), (.voice, true)], any],
  [M [(.continuant, false), (.anterior, false)], any],
  [any, M [(.back, false)]],
  [M [(.anterior, true), (.strident, true)], M [(.anterior, false)]],
  [M [(.spreadGlottis, true)], M' [(.back, true)]],
  [M [(.continuant, true), (.voice, true), (.coronal, true)]],
  [M [(.voice, true)], M' [(.approximant, true), (.coronal, true)]],
  [M [(.continuant, true), (.strident, false)], M' [(.approximant, true), (.anterior, false)]],
  [any, M' [(.continuant, false), (.voice, false), (.labial, true)], M [(.consonantal, true)]],
  [any, M [(.coronal, true)], M' [(.approximant, true), (.anterior, false)]],
  [M [(.continuant, true), (.strident, false)]],
  [M [(.strident, true)], M [(.anterior, false)]],
  [M [(.continuant, false), (.voice, false), (.coronal, true)],
    M' [(.approximant, true), (.anterior, false)]]]

/-- The weights of Table 4, in hundredths. -/
def table4W : Fin 23 → ℕ :=
  ![564, 328, 591, 517, 537, 666, 440, 131, 496, 484, 484, 317, 504, 280, 482, 269, 297, 206,
    305, 206, 184, 210, 170]

open Seg

/-- The score (4) of an onset under the learned grammar, in hundredths. -/
def h (o : List Seg) : ℕ := score Seg.spec table4 table4W o

/-- The violations of the `k`-th constraint of Table 4 (numbered from 1) on an onset. -/
def viol (k : Fin 23) (o : List Seg) : ℕ := (table4 k).violations Seg.spec o

/-- The learning data (11): the onsets of the nonexotic corpus, read off the rows. -/
def attested : List (List Seg) :=
  Examples.all.filterMap λ e =>
    if e.feature? "corpus" = some "(11)" then Seg.parse e.primaryText.toList else none

/-- Every attested onset is penalized by at most 4.53; most score 0 (§5.3.1). -/
theorem attested_le : ∀ o ∈ attested, h o ≤ 453 := by decide

/-- §5.3.1: exactly ten of the attested onsets receive penalties, the rarest ones, in the
    corpus order of (11): [θ], [z], [θr], [tw], [ʃr], [ð], [dw], [gw], [θw], [skl]. -/
theorem attested_penalized :
    (attested.filter (h · ≠ 0)).map (λ o => (o, h o)) =
      [([th], 184), ([z], 269), ([th, r], 184), ([t, w], 170), ([sh, r], 210), ([dh], 453),
        ([d, w], 297), ([g, w], 297), ([th, w], 390), ([s, k, l], 305)] := by decide

/-- The twelve unattested onsets with the best scores (§5.3.1). -/
def twelve : List (List Seg) :=
  [[s, t, w], [d, l], [hh, l], [hh, r], [v, l], [v, r], [sh, l], [sh, w], [s, r], [f, w], [p, w],
    [s, p, w]]

/-- §5.3.1: [stw] 3.76, the accidental gap, then [dl] 4.40, [hl] and [hr] 4.82, [vl], [vr],
    [ʃl], [ʃw] 4.84, [sr] 4.90, [fw], [pw], [spw] 4.96. -/
theorem twelve_scores :
    twelve.map h = [376, 440, 482, 482, 484, 484, 484, 484, 490, 496, 496, 496] := by decide

/-- Most unattested onsets score far worse: [rt] 21.81, from #3, #6, #7, and #10. -/
theorem h_rt : h [r, t] = 2181 ∧ viol 2 [r, t] = 1 ∧ viol 5 [r, t] = 1 ∧ viol 6 [r, t] = 1 ∧
    viol 9 [r, t] = 1 := by decide

/-- The gang of §5.2: #8, #14, and #22, each weighted below the threshold of about 4, together
    give *[stʃ] the bad score 6.21. -/
theorem stch_gang :
    h [s, ch] = 621 ∧ viol 7 [s, ch] = 1 ∧ viol 13 [s, ch] = 1 ∧ viol 21 [s, ch] = 1 ∧
      table4W 7 < 400 ∧ table4W 13 < 400 ∧ table4W 21 < 400 := by decide

/-- #2 ganging with #16 rules out *[ʒ]. -/
theorem zh_gang : h [zh] = 597 ∧ viol 1 [zh] = 1 ∧ viol 15 [zh] = 1 := by decide

/-- #18 and #21 gang to penalize the especially rare attested onset [θw]. -/
theorem thw_gang : h [th, w] = 390 ∧ viol 17 [th, w] = 1 ∧ viol 20 [th, w] = 1 := by decide

/-- A decimal numeral. -/
private def digits (cs : List Char) : Option ℕ :=
  if cs ≠ [] ∧ cs.all Char.isDigit then
    some (cs.foldl (λ n c => 10 * n + (c.toNat - '0'.toNat)) 0)
  else none

/-- A reported score, a two-decimal numeral, in hundredths. -/
def hundredths (s : String) : Option ℕ :=
  match s.toList.span (· ≠ '.') with
  | (whole, '.' :: frac) => (digits whole).bind λ x => (digits frac).map λ y => 100 * x + y
  | _ => none

/-- A row that reports a score is reproduced: its onset parses and the grammar's score is
    within one hundredth of the reported one. -/
def Reproduced (e : LinguisticExample) : Prop :=
  ∀ sc ∈ e.feature? "score", ∃ o ∈ Seg.parse e.primaryText.toList, ∃ k ∈ hundredths sc,
    ((h o : ℤ) - k).natAbs ≤ 1

instance : DecidablePred Reproduced := λ e => by unfold Reproduced; infer_instance

/-- Every score the paper reports (§5.2–5.3) is reproduced by the grammar to within one
    hundredth, the rounding of the printed weights. -/
theorem rows_scores : ∀ e ∈ Examples.all, Reproduced e := by decide +kernel

/-! ### Probability over a candidate set (§3.2, (6)) -/

/-- The candidate set: the attested onsets and the unattested ones discussed. -/
def candidates : Finset (List Seg) :=
  (attested ++ twelve ++ [[r, t], [s, ch], [zh]]).toFinset

/-- The learned grammar as a probability model over the candidate set: the score is the
    negated score (4) and the decoder is the softmax of (6). -/
noncomputable def onsetSystem : Core.Optimization.ConstraintSystem (List Seg) ℝ where
  candidates := candidates
  score o := -(h o : ℝ) / 100
  decoder := Core.Optimization.softmaxDecoder 1

/-- On the candidate set, the probability (6) orders forms as the score does. -/
theorem predict_lt_of_h_lt {o₁ o₂ : List Seg} (h₁ : o₁ ∈ candidates)
    (h₂ : o₂ ∈ candidates)
    (hlt : h o₂ < h o₁) : onsetSystem.predict o₁ < onsetSystem.predict o₂ :=
  Core.Optimization.ConstraintSystem.predict_softmax_lt_of_score_lt _ one_pos rfl h₁ h₂ (by
    simp only [onsetSystem]
    rw [div_lt_div_iff_of_pos_right (by norm_num), neg_lt_neg_iff, Nat.cast_lt]
    exact hlt)

/-- The accidental gap [stw] is more probable than [rt]. -/
theorem predict_rt_lt_stw : onsetSystem.predict [r, t] < onsetSystem.predict [s, t, w] :=
  predict_lt_of_h_lt (by decide) (by decide) (by decide)

/-- The probabilities sum to one over the candidate set. -/
theorem onsetSystem_sum : ∑ c ∈ candidates, onsetSystem.predict c = 1 :=
  Core.Optimization.ConstraintSystem.predict_softmax_isProb _ rfl ⟨[r, t], by decide⟩

end HayesWilson2008
