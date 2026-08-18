import Linglib.Phonology.Constraints.Defs
import Linglib.Core.Probability.CoupledEvaluation
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

open Constraints Phonology Farsi.Phonology

/-! ### Systemic Constraints -/

/-- A **systemic constraint** evaluates a whole output *tuple* — one output per
    input — rather than an individual input→output pair, so it cannot be
    decomposed into per-mapping evaluations (e.g. \*HOMOPHONY counts colliding
    output pairs). Like a `Constraint`, it *is* its violation-counting function;
    its weight is supplied separately (the systemic twin of an HG weight). -/
abbrev SystemicConstraint (n : Nat) (O : Type*) := (Fin n → O) → ℕ

/-- \*HOMOPHONY: penalizes output tuples where distinct inputs receive the same
    output, counting the colliding pairs `|{(i, j) : i < j ∧ f i = f j}|`. -/
def homophonyAvoidance {n : Nat} {O : Type*} [DecidableEq O] :
    SystemicConstraint n O :=
  fun f =>
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ f p.1 = f p.2).card

/-- On a two-item paradigm, \*HOMOPHONY is the collision indicator. -/
theorem homophonyAvoidance_pair {O : Type*} [DecidableEq O] (a b : O) :
    homophonyAvoidance (n := 2) ![a, b] = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    have : (Finset.univ.filter
        fun p : Fin 2 × Fin 2 => p.1 < p.2 ∧ ![a, a] p.1 = ![a, a] p.2)
        = {(0, 1)} := by
      ext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp +decide
    simp [homophonyAvoidance, this]
  · have : (Finset.univ.filter
        fun p : Fin 2 × Fin 2 => p.1 < p.2 ∧ ![a, b] p.1 = ![a, b] p.2)
        = ∅ := by
      ext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp +decide [h]
    simp [homophonyAvoidance, this, h]

/-! ### Joint Distribution with Systemic Constraints -/

/-- **Systemic harmony** of an output tuple: `-∑ⱼ swⱼ · sconⱼ(f)`, the negated
    weighted sum of the systemic constraints' tuple-violation counts. The
    systemic twin of `harmonyScore` — same negated-weighted-sum shape, but
    scoring whole tuples; it is the coupling component of the joint score. -/
def systemicScore {n k : Nat} {O : Type*}
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O) (f : Fin n → O) : ℝ :=
  -∑ j, sw j * (scon j f : ℝ)

/-- Joint harmony score over the product space, combining classical per-mapping
    scores with the systemic tuple-level score:
    `H_joint(f) = ∑ᵢ H(iᵢ, f i) + systemicScore sw scon f`. -/
noncomputable def jointHarmonyScore {n m k : Nat} {I O : Type*}
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O)
    (f : Fin n → O) : ℝ :=
  (List.finRange n).foldl
    (λ acc i => acc + harmonyScore classicalCon classicalW (inputs i, f i)) 0
  + systemicScore sw scon f

/-- MaxEnt grammar with systemic constraints as a `CoupledSoftmax`:
    `componentScore i v = harmonyScore classicalCon classicalW (inputs i, v)` and
    `couplingScore f = systemicScore sw scon f`. The joint probability is a
    softmax over all `Fin n → O` output tuples; its marginal at position `i`
    recovers the individual mapping probability under systemic pressure. -/
noncomputable def maxEntCoupled {n m k : Nat} {I O : Type*} [Fintype O] [DecidableEq O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O) :
    CoupledSoftmax (Fin n) O :=
  coupledSoftmaxOfMaxEnt inputs
    (fun p => harmonyScore classicalCon classicalW p)
    (fun f => systemicScore sw scon f)

/-- Marginal probability `P(oᵢ ∣ iᵢ) = ∑_{f : f i = oᵢ} P_joint(f)`: marginalize
    the joint distribution to recover a specific mapping's probability under
    systemic pressure ([storme-2026]'s key equation). Defined through
    `CoupledSoftmax.marginal` so that factorization follows from
    `marginal_eq_independent_when_uncoupled`. -/
noncomputable def marginalProb {n m k : Nat} {I O : Type*} [Fintype O] [DecidableEq O]
    [Nonempty O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O)
    (i : Fin n) (o : O) : ℝ :=
  (maxEntCoupled inputs classicalCon classicalW sw scon).marginal i o

/-! ### Factorization Theorem -/

/-- When all systemic weights are zero, the systemic score vanishes on every
    output tuple. -/
private lemma systemicScore_zero {n k : Nat} {O : Type*}
    {sw : Fin k → ℝ} (h_zero : ∀ j, sw j = 0)
    (scon : Fin k → SystemicConstraint n O) (f : Fin n → O) :
    systemicScore sw scon f = 0 := by
  simp only [systemicScore, h_zero, zero_mul, Finset.sum_const_zero, neg_zero]

/-- **Factorization**: when systemic weights are all zero, the marginal equals
    the classical MaxEnt probability. The coupling score is then constant (= 0),
    so `marginal_eq_independent_when_uncoupled` applies: the joint factorizes and
    each marginal equals its independent per-item softmax. -/
theorem marginal_eq_classical_when_no_systemic {n m k : Nat} {I O : Type*}
    [Fintype O] [DecidableEq O] [Nonempty O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O)
    (h_zero : ∀ j, sw j = 0)
    (i : Fin n) (o : O) :
    marginalProb inputs classicalCon classicalW sw scon i o =
    softmax (λ o' => harmonyScore classicalCon classicalW (inputs i, o')) o :=
  (maxEntCoupled inputs classicalCon classicalW sw scon).marginal_eq_independent_when_uncoupled
    ⟨0, systemicScore_zero h_zero scon⟩ i o


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
