import Linglib.Phonology.HarmonicGrammar.MaxEnt
import Linglib.Phonology.Segmental.Defs
import Linglib.Phonology.Hiatus
import Linglib.Fragments.Farsi.Phonology
import Linglib.Core.Probability.LogitChoice
import Mathlib.Data.Fin.VecNotation

/-!
# Storme (2026) [storme-2026]

*A method to evaluate systemic constraints in probabilistic grammars*:
systemic constraints — \*Homophony and others that score several
input–output mappings jointly — become compatible with probabilistic
grammars by evaluating a MaxEnt distribution over joint output tuples and
marginalizing to recover individual mapping probabilities. The case study is
variable hiatus in spoken Persian ([ariyaee-jurgec-2021]): the suffix vowel
deletes freely in /hutʃɑ-emun/ (1PL possessive) but rarely in /hutʃɑ-e/
(definite), where deletion would leave the suffixed form homophonous with
the bare stem. This file builds the paradigm from Persian segment strings
with the resolutions as juncture operations — homophony is string identity,
and the suffix-length conditioning is string algebra
(`Hiatus.elideV2_eq_left_iff`) — and derives the closed form of the
marginalized model (`persianMarginal_eq_softmax`), its fitted-weight
preference orders (Table 5), and the suffix-length effect that \*Homophony
creates (`homophony_length_effect`) and classical constraints cannot
(`classical_no_length_effect`).
-/

namespace Storme2026

open Constraints HarmonicGrammar Phonology Farsi.Phonology

/-! ### The paradigm as segment strings -/

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

/-- The stem /hutʃɑ/. -/
def stem : List Segment := [h, u, ch, aa]

/-- The segmental content of each suffix: the definite suffix -e against the
1PL possessive -emun. -/
def suffix : HiatusInput → List Segment
  | .mono => [e]
  | .poly => [e, m, u, n]

/-- The underlying form: stem plus suffix. -/
def underlying (i : HiatusInput) : List Segment := stem ++ suffix i

/-- The three hiatus resolutions as `Hiatus` repairs at the stem–suffix
juncture: faithful concatenation, glottal-stop epenthesis, V2 elision. -/
def resolve : HiatusOutput → List Segment → List Segment → List Segment
  | .hiatus => (· ++ ·)
  | .epenthesis => Hiatus.epenthesize glottal
  | .deletion => Hiatus.elideV2

/-- The surface form of each mapping, computed from the string operations. -/
def realize (i : HiatusInput) (o : HiatusOutput) : List Segment :=
  resolve o stem (suffix i)

/-- [hutʃɑ]: deletion under the monosegmental suffix *is* the bare stem — the
concrete instance of `Hiatus.elideV2_eq_left_iff`. -/
theorem realize_mono_deletion : realize .mono .deletion = stem := rfl

/-- [hutʃɑmun]: deletion under the polysegmental suffix keeps a residue
distinct from the stem. -/
theorem realize_poly_deletion_ne_stem : realize .poly .deletion ≠ stem := by
  decide

/-! ### Constraints computed on strings, and the fitted weights -/

/-- \*Hiatus: vowel–vowel adjacencies surviving in the surface form. -/
def starHiatus : Constraint (HiatusInput × HiatusOutput) := fun c =>
  Hiatus.count (realize c.1 c.2)

/-- Dep: inserted segments — the surface form's length excess over the
underlying form. Length-based counting is exact for this candidate set, since
every candidate differs from the underlying form by pure insertion or pure
deletion. -/
def depConstraint : Constraint (HiatusInput × HiatusOutput) := fun c =>
  (realize c.1 c.2).length - (underlying c.1).length

/-- Max: deleted segments — the underlying form's length excess over the
surface form. -/
def maxConstraint : Constraint (HiatusInput × HiatusOutput) := fun c =>
  (underlying c.1).length - (realize c.1 c.2).length

/-- The string-computed \*Hiatus reproduces its binary Table 4 column. -/
theorem starHiatus_eq (i : HiatusInput) (o : HiatusOutput) :
    starHiatus (i, o) = if o = .hiatus then 1 else 0 := by
  revert i o; decide

/-- The string-computed Dep reproduces its binary Table 4 column. -/
theorem depConstraint_eq (i : HiatusInput) (o : HiatusOutput) :
    depConstraint (i, o) = if o = .epenthesis then 1 else 0 := by
  revert i o; decide

/-- The string-computed Max reproduces its binary Table 4 column. -/
theorem maxConstraint_eq (i : HiatusInput) (o : HiatusOutput) :
    maxConstraint (i, o) = if o = .deletion then 1 else 0 := by
  revert i o; decide

/-- The joint tableau's inputs, indexed for `marginalProb`. -/
def inputs : Fin 2 → HiatusInput := ![.mono, .poly]

/-- The classical (per-mapping) constraint vector: Dep, \*Hiatus, Max. -/
def classicalCon : CON (HiatusInput × HiatusOutput) 3 :=
  ![depConstraint, starHiatus, maxConstraint]

/-- Fitted weights (posterior means) from [storme-2026]'s Table 4:
Dep = 2.47, \*Hiatus = 1.89, Max = 1 (fixed rather than estimated). -/
noncomputable def classicalW : Fin 3 → ℝ := ![2.47, 1.89, 1]

/-- Fitted weight (posterior mean) of \*Homophony: 2.27. -/
noncomputable def homophonyWeight : ℝ := 2.27

/-- \*Homophony over the paradigm: collisions among the surface forms of the
fixed base (the bare stem) and the two suffixed inputs, via the generic
`homophonyAvoidance`. Homophony is string identity — nothing is stipulated
about which outputs collide. -/
def starHomophony : SystemicConstraint 2 HiatusOutput := fun f =>
  homophonyAvoidance (Matrix.vecCons stem fun i => realize (inputs i) (f i))

/-! ### \*Homophony decomposes over this paradigm -/

/-- Collisions between one realized output and the bare stem. -/
def baseCollisions (i : HiatusInput) (o : HiatusOutput) : ℕ :=
  homophonyAvoidance ![stem, realize i o]

/-- Only deletion of the monosegmental suffix collides with the base — the
concrete instance of `resolve_deletion_eq_stem_iff`. -/
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

/-- Closed form of the folded scores: each repair's fitted cost, with the
\*Homophony penalty (2.27, on top of Max's 1) landing exactly on
monosegmental deletion. -/
theorem foldedScore_eq (i : HiatusInput) (o : HiatusOutput) :
    foldedScore i o = -(match i, o with
      | _, .hiatus => 1.89
      | _, .epenthesis => 2.47
      | .mono, .deletion => 3.27
      | .poly, .deletion => 1) := by
  cases i <;> cases o <;>
    norm_num [foldedScore, baseCollisions_eq, harmonyScore_eq_neg_sum,
      Fin.sum_univ_three, classicalCon, classicalW, homophonyWeight,
      depConstraint_eq, starHiatus_eq, maxConstraint_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

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

Table 5's preference orders: hiatus .55 ≻ epenthesis .31 ≻ deletion .14 under
the monosegmental suffix, deletion .61 ≻ hiatus .25 ≻ epenthesis .14 under
the polysegmental one. -/

/-- A marginal comparison reduces to comparing folded scores. -/
theorem persianMarginal_lt_of_foldedScore_lt {i : Fin 2} {o o' : HiatusOutput}
    (h : foldedScore (inputs i) o < foldedScore (inputs i) o') :
    persianMarginal i o < persianMarginal i o' := by
  rw [persianMarginal_eq_softmax, persianMarginal_eq_softmax]
  exact softmax_strict_mono _ _ _ h

/-- Monosegmental suffix: deletion — which would merge the suffixed form with
the bare stem — is the least likely realization (.14). -/
theorem mono_deletion_lt_epenthesis :
    persianMarginal 0 .deletion < persianMarginal 0 .epenthesis :=
  persianMarginal_lt_of_foldedScore_lt (by norm_num [foldedScore_eq, inputs])

/-- Monosegmental suffix: faithful hiatus is the preferred realization (.55). -/
theorem mono_epenthesis_lt_hiatus :
    persianMarginal 0 .epenthesis < persianMarginal 0 .hiatus :=
  persianMarginal_lt_of_foldedScore_lt (by norm_num [foldedScore_eq, inputs])

/-- Polysegmental suffix: epenthesis is less likely than faithful hiatus
(.14 vs .25). -/
theorem poly_epenthesis_lt_hiatus :
    persianMarginal 1 .epenthesis < persianMarginal 1 .hiatus :=
  persianMarginal_lt_of_foldedScore_lt (by norm_num [foldedScore_eq, inputs])

/-- Polysegmental suffix: deletion is the preferred realization (.61) —
[hutʃɑmun] keeps the suffix recoverable, so \*Homophony is silent. -/
theorem poly_hiatus_lt_deletion :
    persianMarginal 1 .hiatus < persianMarginal 1 .deletion :=
  persianMarginal_lt_of_foldedScore_lt (by norm_num [foldedScore_eq, inputs])

/-! ### The suffix-length effect -/

/-- The classical constraints assess only the repair, so harmony is
input-blind. -/
theorem harmonyScore_input_blind (w : Fin 3 → ℝ) (i i' : HiatusInput)
    (o : HiatusOutput) :
    harmonyScore classicalCon w (i, o) = harmonyScore classicalCon w (i', o) := by
  simp only [harmonyScore_eq_neg_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  fin_cases j <;>
    simp [classicalCon, depConstraint_eq, starHiatus_eq, maxConstraint_eq]

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
  · norm_num [foldedScore_eq, inputs]
  · cases o <;> simp_all [foldedScore_eq, inputs]

end Storme2026
