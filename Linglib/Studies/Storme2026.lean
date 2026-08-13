import Linglib.Phonology.HarmonicGrammar.MaxEnt
import Linglib.Core.Probability.LogitChoice
import Mathlib.Data.Fin.VecNotation

/-!
# [storme-2026]: Systemic Constraints in Probabilistic Grammars

[storme-2026] shows how to evaluate **systemic constraints** — constraints such
as \*Homophony that score several input–output mappings jointly — in
probabilistic constraint-based grammars: take the MaxEnt distribution over
joint output tuples and recover each individual mapping's probability by
marginalization (`HarmonicGrammar.marginalProb`).

The case study is variable vowel hiatus in spoken Persian
([ariyaee-jurgec-2021]): a vowel-initial suffix after a vowel-final stem
(/hutʃɑ-e/ with the definite suffix, /hutʃɑ-emun/ with the 1PL possessive) is
realized faithfully ([hutʃɑe]), with glottal-stop epenthesis ([hutʃɑʔe]), or
with suffix-vowel deletion ([hutʃɑ]). Deletion is the majority outcome for the
polysegmental suffix but rare for the monosegmental one, where it would leave
the suffixed form homophonous with the bare stem. Storme's Table 4 evaluates
\*Homophony jointly over the paradigm with weights fitted to Ariyaee &
Jurgec's frequencies; marginalization (his Table 5) recovers the per-suffix
realization probabilities.

## Main results

* `starHomophony_eq_sum`: over this paradigm \*Homophony decomposes into
  per-input collision counts against the fixed base — the formal content of
  [storme-2026]'s observation (his fn. 1) that [ariyaee-jurgec-2021]'s own
  per-mapping analysis needs no joint evaluation on these data.
* `persianMarginal_eq_softmax`: closed form for the marginalized mapping
  probabilities, via `CoupledSoftmax.marginal_congr` plus the factorization
  theorem.
* `mono_epenthesis_lt_hiatus` &c.: the fitted weights predict the observed
  preference order among the three realizations of each suffix.
* `classical_no_length_effect` and `homophony_length_effect`: without
  \*Homophony the model assigns both suffixes identical distributions whatever
  the weights; with it, deletion is strictly less probable for the
  monosegmental suffix.
-/

namespace Storme2026

open Constraints HarmonicGrammar

/-! ### The Persian hiatus paradigm -/

/-- The two suffixed inputs of [ariyaee-jurgec-2021]'s paradigm: a vowel-final
stem plus a vowel-initial suffix, distinguished by suffix length. -/
inductive HiatusInput where
  /-- /hutʃɑ-e/ — the monosegmental definite suffix. -/
  | mono
  /-- /hutʃɑ-emun/ — the polysegmental 1PL possessive suffix. -/
  | poly
  deriving DecidableEq, Fintype, Repr

/-- The three attested realizations of a suffixed input. -/
inductive HiatusOutput where
  /-- Faithful vowel hiatus, e.g. [hutʃɑe]. -/
  | hiatus
  /-- Glottal-stop epenthesis, e.g. [hutʃɑʔe]. -/
  | epenthesis
  /-- Suffix-vowel deletion, e.g. [hutʃɑ], [hutʃɑmun]. -/
  | deletion
  deriving DecidableEq, Fintype, Inhabited, Repr

instance : Nontrivial HiatusOutput := ⟨.hiatus, .deletion, by decide⟩

/-- The distinct surface forms of the paradigm. Suffix-vowel deletion realizes
/hutʃɑ-e/ as `bare` — the homophony with the unsuffixed stem that
[ariyaee-jurgec-2021] show speakers avoid — whereas /hutʃɑ-emun/ keeps the
residue [hutʃɑmun], distinct from the stem. -/
inductive Surface where
  /-- [hutʃɑ] — the bare stem, and the deletion output of /hutʃɑ-e/. -/
  | bare
  /-- [hutʃɑe] — faithful realization of /hutʃɑ-e/. -/
  | hiatusMono
  /-- [hutʃɑʔe] — epenthesized realization of /hutʃɑ-e/. -/
  | glottalMono
  /-- [hutʃɑemun] — faithful realization of /hutʃɑ-emun/. -/
  | hiatusPoly
  /-- [hutʃɑʔemun] — epenthesized realization of /hutʃɑ-emun/. -/
  | glottalPoly
  /-- [hutʃɑmun] — deletion output of /hutʃɑ-emun/. -/
  | clippedPoly
  deriving DecidableEq, Repr

/-- Surface realization of each mapping. The only clause landing on an
already-occupied form is deletion for `mono`: [hutʃɑ] is the bare stem. -/
def realize : HiatusInput → HiatusOutput → Surface
  | .mono, .hiatus => .hiatusMono
  | .mono, .epenthesis => .glottalMono
  | .mono, .deletion => .bare
  | .poly, .hiatus => .hiatusPoly
  | .poly, .epenthesis => .glottalPoly
  | .poly, .deletion => .clippedPoly

/-- The joint tableau's inputs, indexed for `marginalProb`. -/
def inputs : Fin 2 → HiatusInput := ![.mono, .poly]

/-! ### Constraints and fitted weights -/

/-- Dep: penalizes glottal-stop epenthesis. -/
def depConstraint : Constraint (HiatusInput × HiatusOutput) :=
  Constraint.binary fun c => c.2 = .epenthesis

/-- \*Hiatus: penalizes a surfacing vowel–vowel sequence. -/
def starHiatus : Constraint (HiatusInput × HiatusOutput) :=
  Constraint.binary fun c => c.2 = .hiatus

/-- Max: penalizes suffix-vowel deletion. -/
def maxConstraint : Constraint (HiatusInput × HiatusOutput) :=
  Constraint.binary fun c => c.2 = .deletion

/-- The classical (per-mapping) constraint vector: Dep, \*Hiatus, Max. -/
def classicalCon : CON (HiatusInput × HiatusOutput) 3 :=
  ![depConstraint, starHiatus, maxConstraint]

/-- Fitted weights (posterior means) from [storme-2026]'s Table 4:
Dep = 2.47, \*Hiatus = 1.89, Max = 1 (fixed rather than estimated). -/
noncomputable def classicalW : Fin 3 → ℝ := ![2.47, 1.89, 1]

/-- Fitted weight (posterior mean) of \*Homophony: 2.27. -/
noncomputable def homophonyWeight : ℝ := 2.27

/-- \*Homophony over the paradigm: collisions among the realized surface forms
of the fixed base and the two suffixed inputs, via the generic
`homophonyAvoidance`. -/
def starHomophony : SystemicConstraint 2 HiatusOutput := fun f =>
  homophonyAvoidance (Matrix.vecCons Surface.bare fun i => realize (inputs i) (f i))

/-! ### \*Homophony decomposes over this paradigm -/

/-- Collisions between one realized output and the fixed base. -/
def baseCollisions (i : HiatusInput) (o : HiatusOutput) : ℕ :=
  homophonyAvoidance ![Surface.bare, realize i o]

/-- Only deletion of the monosegmental suffix collides with the base. -/
theorem baseCollisions_eq (i : HiatusInput) (o : HiatusOutput) :
    baseCollisions i o = if i = .mono ∧ o = .deletion then 1 else 0 := by
  revert i o; decide

/-- Suffixed outputs never collide with one another, so \*Homophony reduces to
the per-input base collisions. This is the formal content of [storme-2026]'s
fn. 1: on these data, an analysis with a per-mapping constraint against null
suffix realization — [ariyaee-jurgec-2021]'s — coincides with the systemic
one. -/
theorem starHomophony_eq_sum (f : Fin 2 → HiatusOutput) :
    starHomophony f = ∑ i, baseCollisions (inputs i) (f i) := by
  revert f; decide

/-! ### Marginalized mapping probabilities -/

/-- Marginal probability that input `i` is realized as `o` — [storme-2026]'s
key marginalization equation instantiated to the Persian paradigm. -/
noncomputable def persianMarginal (i : Fin 2) (o : HiatusOutput) : ℝ :=
  marginalProb inputs classicalCon classicalW ![homophonyWeight] ![starHomophony] i o

/-- Per-input harmony with the base-collision penalty folded in. -/
noncomputable def foldedScore (i : HiatusInput) (o : HiatusOutput) : ℝ :=
  harmonyScore classicalCon classicalW (i, o) - homophonyWeight * baseCollisions i o

/-- The uncoupled equivalent of the Persian model: by `starHomophony_eq_sum`
the coupling folds into the per-input scores. -/
noncomputable def persianUncoupled : CoupledSoftmax (Fin 2) HiatusOutput where
  componentScore i o := foldedScore (inputs i) o
  couplingScore _ := 0

/-- The joint score of the Persian model agrees with its uncoupled
equivalent's on every output tuple. -/
theorem totalScore_eq (f : Fin 2 → HiatusOutput) :
    (maxEntCoupled inputs classicalCon classicalW ![homophonyWeight]
        ![starHomophony]).totalScore f = persianUncoupled.totalScore f := by
  simp only [CoupledSoftmax.totalScore, maxEntCoupled, coupledSoftmaxOfMaxEnt,
    persianUncoupled, foldedScore, systemicScore, starHomophony_eq_sum,
    Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero]
  push_cast
  ring

/-- Closed form for the marginals: the coupling decomposes across positions
(`starHomophony_eq_sum`), so the joint factorizes and each marginal is the
softmax of its folded score. -/
theorem persianMarginal_eq_softmax (i : Fin 2) (o : HiatusOutput) :
    persianMarginal i o = softmax (foldedScore (inputs i)) o :=
  calc persianMarginal i o
      = persianUncoupled.marginal i o :=
        CoupledSoftmax.marginal_congr totalScore_eq i o
    _ = softmax (foldedScore (inputs i)) o :=
        persianUncoupled.marginal_eq_independent_when_uncoupled ⟨0, fun _ => rfl⟩ i o

/-- The marginals form a probability distribution over the three realizations. -/
theorem persianMarginal_sum_eq_one (i : Fin 2) :
    ∑ o : HiatusOutput, persianMarginal i o = 1 :=
  CoupledSoftmax.marginal_sum_eq_one _ i

/-! ### Predictions with the fitted weights

The marginalized model reproduces [ariyaee-jurgec-2021]'s frequencies
([storme-2026] Table 5: hiatus .55 ≻ epenthesis .31 ≻ deletion .14 for the
monosegmental suffix; deletion .61 ≻ hiatus .25 ≻ epenthesis .14 for the
polysegmental one). The theorems verify the predicted preference orders; the
exact fitted frequencies live in the paper's tables. -/

/-- Monosegmental suffix: deletion is the least likely realization (predicted
frequency .14) — it would merge the suffixed form with the bare stem. -/
theorem mono_deletion_lt_epenthesis :
    persianMarginal 0 .deletion < persianMarginal 0 .epenthesis := by
  rw [persianMarginal_eq_softmax, persianMarginal_eq_softmax]
  exact softmax_strict_mono _ _ _ (by
    norm_num [foldedScore, baseCollisions_eq, harmonyScore_eq_neg_sum,
      Fin.sum_univ_three, classicalCon, classicalW, homophonyWeight, depConstraint,
      starHiatus, maxConstraint, inputs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons])

/-- Monosegmental suffix: faithful hiatus is the preferred realization
(predicted frequency .55). -/
theorem mono_epenthesis_lt_hiatus :
    persianMarginal 0 .epenthesis < persianMarginal 0 .hiatus := by
  rw [persianMarginal_eq_softmax, persianMarginal_eq_softmax]
  exact softmax_strict_mono _ _ _ (by
    norm_num [foldedScore, baseCollisions_eq, harmonyScore_eq_neg_sum,
      Fin.sum_univ_three, classicalCon, classicalW, homophonyWeight, depConstraint,
      starHiatus, maxConstraint, inputs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons])

/-- Polysegmental suffix: epenthesis is less likely than faithful hiatus
(predicted frequencies .14 vs .25). -/
theorem poly_epenthesis_lt_hiatus :
    persianMarginal 1 .epenthesis < persianMarginal 1 .hiatus := by
  rw [persianMarginal_eq_softmax, persianMarginal_eq_softmax]
  exact softmax_strict_mono _ _ _ (by
    norm_num [foldedScore, baseCollisions_eq, harmonyScore_eq_neg_sum,
      Fin.sum_univ_three, classicalCon, classicalW, homophonyWeight, depConstraint,
      starHiatus, maxConstraint, inputs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons])

/-- Polysegmental suffix: deletion is the preferred realization (predicted
frequency .61) — [hutʃɑmun] keeps the suffix recoverable, so \*Homophony is
silent. -/
theorem poly_hiatus_lt_deletion :
    persianMarginal 1 .hiatus < persianMarginal 1 .deletion := by
  rw [persianMarginal_eq_softmax, persianMarginal_eq_softmax]
  exact softmax_strict_mono _ _ _ (by
    norm_num [foldedScore, baseCollisions_eq, harmonyScore_eq_neg_sum,
      Fin.sum_univ_three, classicalCon, classicalW, homophonyWeight, depConstraint,
      starHiatus, maxConstraint, inputs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons])

/-! ### The suffix-length effect -/

/-- The classical constraints assess only the output, so harmony is
input-blind (definitionally: every constraint projects the output component). -/
theorem harmonyScore_input_blind (w : Fin 3 → ℝ) (i i' : HiatusInput)
    (o : HiatusOutput) :
    harmonyScore classicalCon w (i, o) = harmonyScore classicalCon w (i', o) := rfl

/-- Without \*Homophony the model cannot express a suffix-length effect: for
any classical weights the two suffixes receive identical distributions. The
qualitative core of [storme-2026]'s model comparison — the fit without
\*Homophony is worse because classical constraints cannot separate the
suffixes at all. -/
theorem classical_no_length_effect (w : Fin 3 → ℝ) (i j : Fin 2) (o : HiatusOutput) :
    marginalProb inputs classicalCon w ![0] ![starHomophony] i o =
      marginalProb inputs classicalCon w ![0] ![starHomophony] j o := by
  rw [marginal_eq_classical_when_no_systemic inputs classicalCon w ![0] ![starHomophony]
      (fun k => by fin_cases k; rfl) i o,
    marginal_eq_classical_when_no_systemic inputs classicalCon w ![0] ![starHomophony]
      (fun k => by fin_cases k; rfl) j o]
  exact congrFun (congrArg softmax (funext fun o' =>
    harmonyScore_input_blind w (inputs i) (inputs j) o')) o

/-- With \*Homophony at its fitted weight, deletion is strictly less probable
for the monosegmental suffix (predicted frequency .14) than for the
polysegmental one (.61): the suffix-length effect of [ariyaee-jurgec-2021]. -/
theorem homophony_length_effect :
    persianMarginal 0 .deletion < persianMarginal 1 .deletion := by
  rw [persianMarginal_eq_softmax, persianMarginal_eq_softmax]
  refine softmax_lt_softmax_of_single_score_lt ?_ fun o ho => ?_
  · norm_num [foldedScore, baseCollisions_eq, harmonyScore_eq_neg_sum,
      Fin.sum_univ_three, classicalCon, classicalW, homophonyWeight, depConstraint,
      starHiatus, maxConstraint, inputs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · cases o with
    | hiatus => rfl
    | epenthesis => rfl
    | deletion => exact absurd rfl ho

end Storme2026
