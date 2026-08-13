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
the bare stem. This file builds the paradigm from two `Hiatus.Juncture`s
over Persian segments — homophony is string identity, and the suffix-length
conditioning is string algebra (`baseCollisions_eq`) — and derives the
closed form of the marginalized model (`persianMarginal_eq_softmax`), its
fitted-weight preference orders (Table 5), and the suffix-length effect that
\*Homophony creates (`homophony_length_effect`) and classical constraints
cannot (`classical_no_length_effect`).
-/

namespace Storme2026

open Constraints HarmonicGrammar Phonology Farsi.Phonology

/-! ### The paradigm: two junctures, three candidate resolutions -/

/-- The three candidate resolutions [ariyaee-jurgec-2021] consider for a
suffixed input — the paper's restriction of the hiatus-resolution typology
([casali-2011]). -/
inductive Resolution where
  /-- Faithful vowel hiatus, e.g. [hutʃɑe]. -/
  | hiatus
  /-- Glottal-stop epenthesis, e.g. [hutʃɑʔe]. -/
  | epenthesis
  /-- Suffix-vowel deletion, e.g. [hutʃɑ], [hutʃɑmun]. -/
  | deletion
  deriving DecidableEq, Fintype, Inhabited, Repr

instance : Nontrivial Resolution := ⟨.hiatus, .deletion, by decide⟩

/-- The definite-suffix juncture /hutʃɑ-e/: monosegmental suffix. -/
def definite : Hiatus.Juncture :=
  ⟨[h, u, ch], aa, e, [], by decide, by decide⟩

/-- The possessive-suffix juncture /hutʃɑ-emun/: polysegmental suffix. -/
def possessive : Hiatus.Juncture :=
  ⟨[h, u, ch], aa, e, [m, u, n], by decide, by decide⟩

/-- The joint tableau's inputs, indexed for `marginalProb`. -/
def inputs : Fin 2 → Hiatus.Juncture := ![definite, possessive]

/-- The bare stem [hutʃɑ]. -/
def stem : List Segment := definite.stem

/-- Each candidate as a `Hiatus.Juncture` repair: faithful hiatus,
glottal-stop epenthesis, V2 elision. -/
def resolve : Resolution → Hiatus.Juncture → List Segment
  | .hiatus => Hiatus.Juncture.input
  | .epenthesis => (Hiatus.Juncture.epenthesize · glottal)
  | .deletion => Hiatus.Juncture.elideV2

/-- [hutʃɑ]: deletion at the monosegmental juncture *is* the bare stem — the
concrete instance of `Hiatus.Juncture.elideV2_eq_stem_iff`. -/
theorem resolve_deletion_definite : resolve .deletion definite = stem := rfl

/-- [hutʃɑmun]: deletion at the polysegmental juncture keeps a residue
distinct from the stem. -/
theorem resolve_deletion_possessive_ne_stem :
    resolve .deletion possessive ≠ stem := by decide

/-! ### Constraints computed on strings, and the fitted weights -/

/-- \*Hiatus: vowel–vowel adjacencies surviving in the surface form. -/
def starHiatus : Constraint (Hiatus.Juncture × Resolution) := fun c =>
  Hiatus.count (resolve c.2 c.1)

/-- Dep: inserted segments — the surface form's length excess over the
input. Length-based counting is exact for this candidate set, since every
candidate differs from the input by pure insertion or pure deletion. -/
def depConstraint : Constraint (Hiatus.Juncture × Resolution) := fun c =>
  (resolve c.2 c.1).length - c.1.input.length

/-- Max: deleted segments — the input's length excess over the surface
form. -/
def maxConstraint : Constraint (Hiatus.Juncture × Resolution) := fun c =>
  c.1.input.length - (resolve c.2 c.1).length

/-- Dep's string count reproduces its binary Table 4 column — for any
juncture. -/
theorem depConstraint_eq (j : Hiatus.Juncture) (o : Resolution) :
    depConstraint (j, o) = if o = .epenthesis then 1 else 0 := by
  cases o <;>
    (simp [depConstraint, resolve, Hiatus.Juncture.input, Hiatus.Juncture.stem,
      Hiatus.Juncture.epenthesize, Hiatus.Juncture.elideV2]; all_goals omega)

/-- Max's string count reproduces its binary Table 4 column — for any
juncture. -/
theorem maxConstraint_eq (j : Hiatus.Juncture) (o : Resolution) :
    maxConstraint (j, o) = if o = .deletion then 1 else 0 := by
  cases o <;>
    (simp [maxConstraint, resolve, Hiatus.Juncture.input, Hiatus.Juncture.stem,
      Hiatus.Juncture.epenthesize, Hiatus.Juncture.elideV2]; all_goals omega)

/-- \*Hiatus's string count reproduces its binary Table 4 column on the
paradigm's junctures. Unlike Dep and Max this depends on their segmental
content: hiatus must survive nowhere but the juncture itself. -/
theorem starHiatus_eq (k : Fin 2) (o : Resolution) :
    starHiatus (inputs k, o) = if o = .hiatus then 1 else 0 := by
  revert k o; decide

/-- The classical (per-mapping) constraint vector: Dep, \*Hiatus, Max. -/
def classicalCon : CON (Hiatus.Juncture × Resolution) 3 :=
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
def starHomophony : SystemicConstraint 2 Resolution := fun f =>
  homophonyAvoidance (Matrix.vecCons stem fun k => resolve (f k) (inputs k))

/-! ### \*Homophony decomposes over this paradigm -/

/-- Collisions between one realized output and its juncture's own bare
stem. -/
def baseCollisions (j : Hiatus.Juncture) (o : Resolution) : ℕ :=
  homophonyAvoidance ![j.stem, resolve o j]

/-- Only deletion at a monosegmental juncture collides with the base — for
any juncture, by the string algebra (`Hiatus.Juncture.elideV2_eq_stem_iff`
and the length facts). -/
theorem baseCollisions_eq (j : Hiatus.Juncture) (o : Resolution) :
    baseCollisions j o = if o = .deletion ∧ j.suffixBody = [] then 1 else 0 := by
  cases o with
  | hiatus =>
      simp [baseCollisions, resolve, homophonyAvoidance_pair,
        Ne.symm j.input_ne_stem]
  | epenthesis =>
      simp [baseCollisions, resolve, homophonyAvoidance_pair,
        Ne.symm (j.epenthesize_ne_stem glottal)]
  | deletion =>
      simp [baseCollisions, resolve, homophonyAvoidance_pair, eq_comm]

/-- Suffixed outputs never collide with one another, so \*Homophony reduces
to the per-input base collisions. This is the formal content of
[storme-2026]'s fn. 1: on these data, an analysis with a per-mapping
constraint against null suffix realization — [ariyaee-jurgec-2021]'s —
coincides with the systemic one. -/
theorem starHomophony_eq_sum (f : Fin 2 → Resolution) :
    starHomophony f = ∑ k, baseCollisions (inputs k) (f k) := by
  revert f; decide

/-! ### Marginalized mapping probabilities -/

/-- Marginal probability that input `k` is realized as `o` — [storme-2026]'s
key marginalization equation instantiated to the Persian paradigm. -/
noncomputable def persianMarginal (k : Fin 2) (o : Resolution) : ℝ :=
  marginalProb inputs classicalCon classicalW ![homophonyWeight] ![starHomophony] k o

/-- Per-input harmony with the base-collision penalty folded in. -/
noncomputable def foldedScore (j : Hiatus.Juncture) (o : Resolution) : ℝ :=
  harmonyScore classicalCon classicalW (j, o) - homophonyWeight * baseCollisions j o

/-- Closed form of the folded scores: each candidate's fitted cost, with the
\*Homophony penalty (2.27, on top of Max's 1) landing exactly on deletion at
the monosegmental juncture. -/
theorem foldedScore_eq (k : Fin 2) (o : Resolution) :
    foldedScore (inputs k) o = -(match o with
      | .hiatus => 1.89
      | .epenthesis => 2.47
      | .deletion => if k = 0 then 3.27 else 1) := by
  fin_cases k <;> cases o <;>
    simp only [foldedScore, harmonyScore_eq_neg_sum, Fin.sum_univ_three,
      classicalCon, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, depConstraint_eq, starHiatus_eq,
      maxConstraint_eq, baseCollisions_eq] <;>
    norm_num [classicalW, homophonyWeight, inputs, definite, possessive,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- The uncoupled equivalent of the Persian model: by `starHomophony_eq_sum`
the coupling folds into the per-input scores. -/
noncomputable def persianUncoupled : CoupledSoftmax (Fin 2) Resolution where
  componentScore k o := foldedScore (inputs k) o
  couplingScore _ := 0

/-- The joint score of the Persian model agrees with its uncoupled
equivalent's on every output tuple. -/
theorem totalScore_eq (f : Fin 2 → Resolution) :
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
theorem persianMarginal_eq_softmax (k : Fin 2) (o : Resolution) :
    persianMarginal k o = softmax (foldedScore (inputs k)) o :=
  calc persianMarginal k o
      = persianUncoupled.marginal k o :=
        CoupledSoftmax.marginal_congr totalScore_eq k o
    _ = softmax (foldedScore (inputs k)) o :=
        persianUncoupled.marginal_eq_independent_when_uncoupled ⟨0, fun _ => rfl⟩ k o

/-- The marginals form a probability distribution over the three
resolutions. -/
theorem persianMarginal_sum_eq_one (k : Fin 2) :
    ∑ o : Resolution, persianMarginal k o = 1 :=
  CoupledSoftmax.marginal_sum_eq_one _ k

/-! ### Predictions with the fitted weights

Table 5's preference orders: hiatus .55 ≻ epenthesis .31 ≻ deletion .14 under
the monosegmental suffix, deletion .61 ≻ hiatus .25 ≻ epenthesis .14 under
the polysegmental one. -/

/-- A marginal comparison reduces to comparing folded scores. -/
theorem persianMarginal_lt_of_foldedScore_lt {k : Fin 2} {o o' : Resolution}
    (h : foldedScore (inputs k) o < foldedScore (inputs k) o') :
    persianMarginal k o < persianMarginal k o' := by
  rw [persianMarginal_eq_softmax, persianMarginal_eq_softmax]
  exact softmax_strict_mono _ _ _ h

/-- Monosegmental suffix: deletion — which would merge the suffixed form with
the bare stem — is the least likely realization (.14). -/
theorem mono_deletion_lt_epenthesis :
    persianMarginal 0 .deletion < persianMarginal 0 .epenthesis :=
  persianMarginal_lt_of_foldedScore_lt (by norm_num [foldedScore_eq])

/-- Monosegmental suffix: faithful hiatus is the preferred realization
(.55). -/
theorem mono_epenthesis_lt_hiatus :
    persianMarginal 0 .epenthesis < persianMarginal 0 .hiatus :=
  persianMarginal_lt_of_foldedScore_lt (by norm_num [foldedScore_eq])

/-- Polysegmental suffix: epenthesis is less likely than faithful hiatus
(.14 vs .25). -/
theorem poly_epenthesis_lt_hiatus :
    persianMarginal 1 .epenthesis < persianMarginal 1 .hiatus :=
  persianMarginal_lt_of_foldedScore_lt (by norm_num [foldedScore_eq])

/-- Polysegmental suffix: deletion is the preferred realization (.61) —
[hutʃɑmun] keeps the suffix recoverable, so \*Homophony is silent. -/
theorem poly_hiatus_lt_deletion :
    persianMarginal 1 .hiatus < persianMarginal 1 .deletion :=
  persianMarginal_lt_of_foldedScore_lt (by norm_num [foldedScore_eq])

/-! ### The suffix-length effect -/

/-- The two junctures have identical classical constraint profiles: the
classical grammar cannot see the suffix-length difference. -/
theorem harmonyScore_inputs_eq (w : Fin 3 → ℝ) (k k' : Fin 2) (o : Resolution) :
    harmonyScore classicalCon w (inputs k, o) =
      harmonyScore classicalCon w (inputs k', o) := by
  simp only [harmonyScore_eq_neg_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  fin_cases c <;>
    simp [classicalCon, depConstraint_eq, starHiatus_eq, maxConstraint_eq]

/-- Without \*Homophony the model cannot express a suffix-length effect: for
any classical weights the two suffixes receive identical distributions. The
qualitative core of [storme-2026]'s model comparison — the fit without
\*Homophony is worse because classical constraints cannot separate the
suffixes at all. -/
theorem classical_no_length_effect (w : Fin 3 → ℝ) (k k' : Fin 2) (o : Resolution) :
    marginalProb inputs classicalCon w ![0] ![starHomophony] k o =
      marginalProb inputs classicalCon w ![0] ![starHomophony] k' o := by
  rw [marginal_eq_classical_when_no_systemic inputs classicalCon w ![0] ![starHomophony]
      (fun c => by fin_cases c; rfl) k o,
    marginal_eq_classical_when_no_systemic inputs classicalCon w ![0] ![starHomophony]
      (fun c => by fin_cases c; rfl) k' o]
  exact congrFun (congrArg softmax (funext fun o' =>
    harmonyScore_inputs_eq w k k' o')) o

/-- With \*Homophony at its fitted weight, deletion is strictly less probable
for the monosegmental suffix (predicted frequency .14) than for the
polysegmental one (.61): the suffix-length effect of [ariyaee-jurgec-2021]. -/
theorem homophony_length_effect :
    persianMarginal 0 .deletion < persianMarginal 1 .deletion := by
  rw [persianMarginal_eq_softmax, persianMarginal_eq_softmax]
  refine softmax_lt_softmax_of_single_score_lt ?_ fun o ho => ?_
  · norm_num [foldedScore_eq]
  · cases o <;> simp_all [foldedScore_eq]

end Storme2026
