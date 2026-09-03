import Linglib.Phonology.Constraints.Harmony
import Linglib.Phonology.Hiatus
import Linglib.Fragments.Farsi.Phonology
import Linglib.Core.Probability.LogitChoice

/-!
# Storme (2026): systemic constraints in probabilistic grammars

[storme-2026] makes systemic constraints — \*HOMOPHONY and the other
constraints that score several input–output mappings jointly — compatible
with probabilistic constraint-based grammars: evaluate a MaxEnt distribution
over the joint tableau of output tuples, then *marginalize* to recover each
mapping's probability. The case study is variable hiatus resolution in spoken
Persian ([ariyaee-jurgec-2021]): the suffix vowel of /hutʃɑ-emun/ (1PL
possessive) usually deletes, that of /hutʃɑ-e/ (definite) rarely does, since
deleting it would leave the suffixed form homophonous with the bare stem.

The paradigm is built from two `Hiatus.Juncture`s over Persian segments, so
homophony is string identity and the suffix-length conditioning is string
algebra; the joint tableau is \*HOMOPHONY beside the jointly evaluated
classical constraints (`Constraints.CON.joint`), and its marginals are
computed by `sum_softmax_eval_eq`.

## Main definitions

* `homophonyAvoidance`, `starHomophony` — \*HOMOPHONY on output tuples, and
  its instance over the base and the two suffixed forms.
* `definite`, `possessive`, `resolve` — the paradigm's junctures and the
  three candidate repairs.
* `jointCon`, `jointW`, `predicted` — the paper's joint tableau with its
  fitted weights, and the marginalized mapping probabilities.
* `realizeMorpheme` — the per-mapping constraint of [ariyaee-jurgec-2021]'s
  analysis.

## Main results

* `marginal_eq_classical_of_systemic_zero` — with the systemic weights at
  zero, marginalization returns the classical MaxEnt probabilities.
* `starHomophony_eq_joint_realizeMorpheme`, `predicted_eq_softmax` — on this
  paradigm \*HOMOPHONY is the summed REALIZEMORPHEME, so the marginalized
  model coincides with [ariyaee-jurgec-2021]'s classical one (the paper's
  footnote comparing the two analyses).
* `mono_order`, `poly_order`, `deletion_lt_deletion` — the fitted model's
  preference orders and its suffix-length effect.
* `log_odds_deletion_sub` — in log-odds against hiatus, the suffix-length
  effect on deletion is exactly the \*HOMOPHONY weight.
* `classical_no_length_effect` — without \*HOMOPHONY the two suffixes receive
  identical distributions under every weighting.
-/

namespace Storme2026

open Constraints Phonology Farsi.Phonology Finset Real

/-! ### Systemic constraints, joint evaluation, and marginalization -/

/-- \*HOMOPHONY: the number of pairs of distinct inputs receiving identical
outputs. A **systemic** constraint scores a whole output tuple rather than a
single mapping — a `Constraint` on `Fin n → O` that does not decompose over
the mappings. -/
def homophonyAvoidance {n : ℕ} {O : Type*} [DecidableEq O] : Constraint (Fin n → O) :=
  fun f => #{p : Fin n × Fin n | p.1 < p.2 ∧ f p.1 = f p.2}

section Method

variable {ι I O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O] [DecidableEq O] [Nonempty O]
  {m k : ℕ}

/-- The joint MaxEnt grammar — systemic constraints `scon` beside the jointly
evaluated classical constraints `con` — marginalized at input `i`
([storme-2026]'s marginalization equation). With the systemic weights at
zero it returns the classical MaxEnt probability of each mapping: joint
evaluation plus marginalization conservatively extends the classical
pipeline. -/
theorem marginal_eq_classical_of_systemic_zero (inputs : ι → I) (scon : CON (ι → O) k)
    (con : CON (I × O) m) (w : Fin m → ℝ) (i : ι) (o : O) :
    ∑ f with f i = o,
        softmax (harmonyScore (Fin.append scon (con.joint inputs)) (Fin.append 0 w)) f =
      softmax (fun o' => harmonyScore con w (inputs i, o')) o := by
  have : harmonyScore (Fin.append scon (con.joint inputs)) (Fin.append 0 w) =
      fun f => ∑ i, harmonyScore con w (inputs i, f i) :=
    funext fun f => by simp [harmonyScore_append, harmonyScore_joint]
  rw [this]
  exact sum_softmax_eval_eq (fun i o' => harmonyScore con w (inputs i, o')) i o

end Method

/-! ### The Persian paradigm -/

/-- The three candidate realizations of a suffixed input — the
hiatus-resolution typology ([casali-2011]) as restricted by
[ariyaee-jurgec-2021]. -/
inductive Resolution where
  /-- Faithful vowel hiatus, e.g. [hutʃɑe]. -/
  | hiatus
  /-- Glottal-stop epenthesis, e.g. [hutʃɑʔe]. -/
  | epenthesis
  /-- Suffix-vowel deletion, e.g. [hutʃɑ], [hutʃɑmun]. -/
  | deletion
  deriving DecidableEq, Fintype, Inhabited, Repr

instance : Nontrivial Resolution := ⟨.hiatus, .deletion, by decide⟩

/-- The definite-suffix juncture /hutʃɑ-e/: a monosegmental suffix. -/
def definite : Hiatus.Juncture := ⟨[h, u, ch], aa, e, [], by decide, by decide⟩

/-- The possessive-suffix juncture /hutʃɑ-emun/: a polysegmental suffix. -/
def possessive : Hiatus.Juncture := ⟨[h, u, ch], aa, e, [m, u, n], by decide, by decide⟩

/-- The joint tableau's inputs: the definite and the possessive junctures. -/
def inputs : Fin 2 → Hiatus.Juncture := ![definite, possessive]

/-- The surface form of each candidate: faithful hiatus, glottal-stop
epenthesis, or suffix-vowel elision. -/
def resolve : Resolution → Hiatus.Juncture → List Segment
  | .hiatus => Hiatus.Juncture.input
  | .epenthesis => (Hiatus.Juncture.epenthesize · glottal)
  | .deletion => Hiatus.Juncture.elideV2

/-! ### The constraints and the joint tableau -/

/-- \*HIATUS: vowel–vowel adjacencies surviving in the surface form. -/
def starHiatus : Constraint (Hiatus.Juncture × Resolution) := fun c =>
  Hiatus.count (resolve c.2 c.1)

/-- DEP: inserted segments, as the surface form's length excess over the input
(exact here, since each candidate is a pure insertion or a pure deletion). -/
def depConstraint : Constraint (Hiatus.Juncture × Resolution) := fun c =>
  (resolve c.2 c.1).length - c.1.input.length

/-- MAX: deleted segments, as the input's length excess over the surface
form. -/
def maxConstraint : Constraint (Hiatus.Juncture × Resolution) := fun c =>
  c.1.input.length - (resolve c.2 c.1).length

/-- DEP's string count is its binary tableau column, for any juncture. -/
theorem depConstraint_eq (j : Hiatus.Juncture) (o : Resolution) :
    depConstraint (j, o) = if o = .epenthesis then 1 else 0 := by
  cases o <;>
    (simp [depConstraint, resolve, Hiatus.Juncture.input, Hiatus.Juncture.stem,
      Hiatus.Juncture.epenthesize, Hiatus.Juncture.elideV2]; all_goals omega)

/-- MAX's string count is its binary tableau column, for any juncture. -/
theorem maxConstraint_eq (j : Hiatus.Juncture) (o : Resolution) :
    maxConstraint (j, o) = if o = .deletion then 1 else 0 := by
  cases o <;>
    (simp [maxConstraint, resolve, Hiatus.Juncture.input, Hiatus.Juncture.stem,
      Hiatus.Juncture.epenthesize, Hiatus.Juncture.elideV2]; all_goals omega)

/-- \*HIATUS's string count is its binary tableau column on the paradigm's
junctures — unlike DEP and MAX this depends on their segmental content, since
hiatus must survive nowhere but at the juncture itself. -/
theorem starHiatus_eq (k : Fin 2) (o : Resolution) :
    starHiatus (inputs k, o) = if o = .hiatus then 1 else 0 := by
  revert k o; decide

/-- The classical constraint set: DEP, \*HIATUS, MAX. -/
def classicalCon : CON (Hiatus.Juncture × Resolution) 3 :=
  ![depConstraint, starHiatus, maxConstraint]

/-- The fitted classical weights (posterior means; MAX fixed at 1 rather than
estimated). -/
noncomputable def classicalW : Fin 3 → ℝ := ![2.47, 1.89, 1]

/-- \*HOMOPHONY over the paradigm: collisions among the surface forms of the
base — realized faithfully as the bare stem, its only candidate — and of the
two suffixed inputs. Which outputs collide is string identity. -/
def starHomophony : Constraint (Fin 2 → Resolution) := fun f =>
  homophonyAvoidance (Fin.cons definite.stem fun k => resolve (f k) (inputs k))

/-- The fitted \*HOMOPHONY weight (posterior mean). -/
noncomputable def homophonyWeight : ℝ := 2.27

/-- The joint tableau's constraint set: \*HOMOPHONY beside the jointly evaluated
classical constraints — the columns of the paper's Table 4, over its nine
output tuples. -/
def jointCon : CON (Fin 2 → Resolution) 4 :=
  Fin.append ![starHomophony] (classicalCon.joint inputs)

/-- The joint tableau's weights. -/
noncomputable def jointW : Fin 4 → ℝ := Fin.append ![homophonyWeight] classicalW

/-- The marginalized probability that input `k` is realized as `o`: the paper's
marginalization equation on the joint MaxEnt distribution (its Table 5). -/
noncomputable def predicted (k : Fin 2) (o : Resolution) : ℝ :=
  ∑ f with f k = o, softmax (harmonyScore jointCon jointW) f

/-! ### \*HOMOPHONY against REALIZEMORPHEME

[ariyaee-jurgec-2021] analyse the same data with a per-mapping constraint
penalizing a null realization of the suffix ([kurisu-2001]'s
REALIZEMORPHEME) in place of \*HOMOPHONY. [storme-2026] notes that the two
coincide here, and that only the systemic constraint extends to homophony
avoidance not involving a null morpheme. -/

/-- REALIZEMORPHEME: the suffix has a null realization — the suffixed form
surfaces as its bare stem. -/
def realizeMorpheme : Constraint (Hiatus.Juncture × Resolution) :=
  Constraint.binary fun c => resolve c.2 c.1 = c.1.stem

/-- Only deletion at a monosegmental juncture leaves the suffix unrealized —
for any juncture, by the string algebra of `Hiatus.Juncture`. -/
theorem realizeMorpheme_eq (j : Hiatus.Juncture) (o : Resolution) :
    realizeMorpheme (j, o) = if o = .deletion ∧ j.suffixBody = [] then 1 else 0 := by
  cases o <;> simp [realizeMorpheme, resolve, j.input_ne_stem, j.epenthesize_ne_stem]

/-- On this paradigm \*HOMOPHONY is the jointly evaluated REALIZEMORPHEME: the
suffixed forms never collide with each other, only with the base. -/
theorem starHomophony_eq_joint_realizeMorpheme :
    starHomophony = realizeMorpheme.joint inputs := by
  funext f; revert f; decide

/-- [ariyaee-jurgec-2021]'s classical constraint set, REALIZEMORPHEME beside
DEP, \*HIATUS, MAX, with REALIZEMORPHEME at the fitted \*HOMOPHONY weight. -/
def ajCon : CON (Hiatus.Juncture × Resolution) 4 := Matrix.vecCons realizeMorpheme classicalCon

/-- The weights of `ajCon`. -/
noncomputable def ajW : Fin 4 → ℝ := Matrix.vecCons homophonyWeight classicalW

/-- The joint harmony separates over the two inputs, each scored by
[ariyaee-jurgec-2021]'s grammar: the coupling \*HOMOPHONY introduces folds
into the per-mapping scores. -/
theorem harmonyScore_jointCon (f : Fin 2 → Resolution) :
    harmonyScore jointCon jointW f = ∑ k, harmonyScore ajCon ajW (inputs k, f k) := by
  simp [jointCon, jointW, ajCon, ajW, harmonyScore_append, harmonyScore_joint,
    starHomophony_eq_joint_realizeMorpheme, Fin.sum_univ_two]
  ring

/-- The marginalized model is [ariyaee-jurgec-2021]'s classical one: the joint
distribution factorizes over the inputs, so each marginal is the softmax of
its per-mapping scores. -/
theorem predicted_eq_softmax (k : Fin 2) (o : Resolution) :
    predicted k o = softmax (fun o' => harmonyScore ajCon ajW (inputs k, o')) o := by
  unfold predicted
  rw [funext harmonyScore_jointCon]
  exact sum_softmax_eval_eq (fun k o' => harmonyScore ajCon ajW (inputs k, o')) k o

/-- The fitted per-mapping scores: each candidate's cost, with
REALIZEMORPHEME's 2.27 landing on top of MAX's 1 exactly for deletion at the
monosegmental juncture. -/
theorem ajScore_eq (k : Fin 2) (o : Resolution) :
    harmonyScore ajCon ajW (inputs k, o) = -(match o with
      | .hiatus => 1.89
      | .epenthesis => 2.47
      | .deletion => if k = 0 then 3.27 else 1) := by
  fin_cases k <;> cases o <;>
    simp only [ajCon, ajW, classicalCon, classicalW, harmonyScore_cons, harmonyScore_nil,
      realizeMorpheme_eq, depConstraint_eq, starHiatus_eq, maxConstraint_eq] <;>
    norm_num [homophonyWeight, inputs, definite, possessive]

/-! ### Predictions with the fitted weights -/

/-- Monosegmental suffix: hiatus (.55) over epenthesis (.31) over deletion
(.14), which would merge the suffixed form with the bare stem. -/
theorem mono_order :
    predicted 0 .deletion < predicted 0 .epenthesis ∧
      predicted 0 .epenthesis < predicted 0 .hiatus := by
  simp only [predicted_eq_softmax]
  exact ⟨softmax_strict_mono _ _ _ (by norm_num [ajScore_eq]),
    softmax_strict_mono _ _ _ (by norm_num [ajScore_eq])⟩

/-- Polysegmental suffix: deletion (.61) over hiatus (.25) over epenthesis
(.14) — [hutʃɑmun] keeps the suffix recoverable, so \*HOMOPHONY is silent. -/
theorem poly_order :
    predicted 1 .epenthesis < predicted 1 .hiatus ∧
      predicted 1 .hiatus < predicted 1 .deletion := by
  simp only [predicted_eq_softmax]
  exact ⟨softmax_strict_mono _ _ _ (by norm_num [ajScore_eq]),
    softmax_strict_mono _ _ _ (by norm_num [ajScore_eq])⟩

/-- The suffix-length effect of [ariyaee-jurgec-2021]: deletion is less likely
for the monosegmental suffix (.14) than for the polysegmental one (.61). -/
theorem deletion_lt_deletion : predicted 0 .deletion < predicted 1 .deletion := by
  simp only [predicted_eq_softmax]
  refine softmax_lt_softmax_of_single_score_lt ?_ fun o ho => ?_
  · norm_num [ajScore_eq]
  · cases o <;> simp_all [ajScore_eq]

/-- In log-odds against faithful hiatus, deletion is exactly the \*HOMOPHONY
weight less likely under the monosegmental suffix than under the
polysegmental one: the whole suffix-length effect is the systemic penalty. -/
theorem log_odds_deletion_sub :
    log (predicted 1 .deletion / predicted 1 .hiatus) -
      log (predicted 0 .deletion / predicted 0 .hiatus) = homophonyWeight := by
  simp only [predicted_eq_softmax, log_softmax_odds, ajScore_eq]
  norm_num [homophonyWeight]

/-- DEP, \*HIATUS and MAX give the two junctures identical violation
profiles. -/
theorem harmonyScore_classicalCon_inputs (w : Fin 3 → ℝ) (k k' : Fin 2) (o : Resolution) :
    harmonyScore classicalCon w (inputs k, o) = harmonyScore classicalCon w (inputs k', o) :=
  harmonyScore_congr fun j => by
    fin_cases j <;> simp [classicalCon, depConstraint_eq, starHiatus_eq, maxConstraint_eq]

/-- Without \*HOMOPHONY there is no suffix-length effect to fit: the classical
grammar assigns the two suffixes the same distribution under every weighting.
The paper reports the correspondingly worse fit of the model without
\*HOMOPHONY. -/
theorem classical_no_length_effect (w : Fin 3 → ℝ) (o : Resolution) :
    softmax (fun o' => harmonyScore classicalCon w (inputs 0, o')) o =
      softmax (fun o' => harmonyScore classicalCon w (inputs 1, o')) o := by
  simp only [harmonyScore_classicalCon_inputs w 0 1]

end Storme2026
