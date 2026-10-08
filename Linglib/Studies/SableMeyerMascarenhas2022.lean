module

public import Linglib.Processing.Reasoning.Erotetic
public import Linglib.Semantics.Exhaustification.ConjunctiveDisjunct
public import Linglib.Core.Probability.UniformOn
public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Linglib.Data.Examples.SableMeyerMascarenhas2022
public import Linglib.Data.Experiments.SableMeyerMascarenhas2022

/-!
# Sablé-Meyer and Mascarenhas (2022): Indirect illusory inferences from disjunction

This file formalizes the indirect illusory inferences of Sablé-Meyer and Mascarenhas, their
case against the extant accounts of the classical illusion, and the confirmation-theoretic
selection that unifies the deductive fallacies with the conjunction fallacy.

The indirect schema puts a hint `d` that matches no conjunct of the disjunctive premise
`(a ∧ b) ∨ c` but is causally connected to `a` ((2), (6)); the classical schema is its `d = a`
limit (`Erotetic.disjunction_eq_indirect`). Exact matching, the selection procedure of the
mental-models account and the erotetic theory, provably certifies the classical illusion and
nothing in the indirect one (`Erotetic.indirect_not_illusory_matches`, §5.1), yet acceptance of
the indirect fallacy tracks the normed strength of the causal link almost perfectly (slope .97,
R² .9; the matching case is the `P(a|d) = 1` limit, where the model predicts the literature's
.92 — `matching_limit`). The paper's replacement is selection by Bayesian confirmation
(§5.4, after [crupi-fitelson-tentori-2008]): with the Difference measure, independence of `b`
makes `D(a ∧ b, d)` a positive multiple of `D(a, d)` while `D(c, d) = 0`
(`confirmationD_inter_eq_mul`, `confirmationD_eq_zero`), so the first alternative is uniquely
selected (`indirect_bestConfirmed`, with `not_bestConfirmed_right` the asymmetry the bare
overlap rule misses) and the illusion goes through (`indirect_illusory_bestConfirmed`). The
conjunction fallacy is the same selection at the options `(f ∧ b) ∨ b`: `conjunctionFallacy`
is definitionally the indirect schema, and (18)'s parallel is the same lemma instantiated
(`conjunctionFallacy_bestConfirmed`).

Against the rivals: the revised mental model theory's weak necessities (after
[khemlani-byrne-johnson-laird-2018], as the paper states them over the models of (12)) certify
the attractive conclusion *b* and the unattractive *c* symmetrically (`system2_overgenerates`),
against the sharp (13) asymmetry; its System-1 route, gaps behaving as negations under model
conjunction ([johnson-laird-ragni-2019]), interprets the premise as (16)
(`fillGaps_system1P1`), which is exactly the strongly exhaustive reading of [spector-2007]
(`gapNegation_eq_exh`) — [mascarenhas-2014]'s absolving interpretation, under which the
conclusion is valid (`gapNegation_valid`), the pragmatic path whose reality [picat-2019]'s
load data support. The New Paradigm's posteriors cannot separate *b* from *c*
(`Erotetic.posterior_eq_iff`): under independent flat priors both posteriors are 2/3
(`flat_posterior_b`, `flat_posterior_c`), under the exclusive reading both are 1/2
(`exclusive_posterior`), and neither conclusion is p-valid under either reading (`not_pValid`).
The experiments' printed statistics live in `Data.Experiments.SableMeyerMascarenhas2022`; the
seven surviving items are counted by `items_kept_card`.

## Implementation notes

* Selection rules are predicates on alternatives (`Erotetic.Problem.Illusory`); the paper's
  matching-versus-confirmation contrast is two rules for one schema.
* The independence the §5.4 argument needs is `b ⟂ a` and `b ⟂ (a ∩ d)` as `IndepSet`s,
  stronger than the printed "b and d are independent by design"; the supplement's proof is not
  in the article.
* §5.3's exclusive reading is the XOR of the disjuncts (`Exor_eq_symmDiff`), not §5.2.2's
  strongly exhaustive (16), under which the posteriors do separate the conclusions.
* A mental model is a partial assignment `Atom → Option Bool`, model inclusion is literal
  inclusion, and `BestConfirmed` is a strict argmax; the paper does not discuss ties.

## TODO

* The paper notes the selection asymmetry holds for all confirmation measures of
  [tentori-crupi-bonini-osherson-2007]; only the Difference measure is formalized.
* The graded conclusion step of Experiment 2 ((10): conclude `a` from the selected `b ∧ d`
  via the causal link) has no formal account in the paper; `exp2_illusory_a` states the
  deterministic limit `d ⊆ a`.

## References

* [M. Sablé-Meyer and S. Mascarenhas, *Indirect illusory inferences from disjunction: a new
  bridge between deductive inference and representativeness*
  (2022)][sable-meyer-mascarenhas-2022]
* [C. Walsh and P. N. Johnson-Laird, *Co-reference and reasoning*
  (2004)][walsh-johnson-laird-2004]
* [P. N. Johnson-Laird and F. Savary, *Illusory inferences: a novel class of erroneous
  deductions* (1999)][johnson-laird-savary-1999]
* [P. Koralus and S. Mascarenhas, *The erotetic theory of reasoning*
  (2013)][koralus-mascarenhas-2013]
* [S. Khemlani, R. Byrne and P. N. Johnson-Laird, *Facts and Possibilities: A Model-Based
  Theory of Sentential Reasoning* (2018)][khemlani-byrne-johnson-laird-2018]
* [P. N. Johnson-Laird and M. Ragni, *Possibilities as the foundation of reasoning*
  (2019)][johnson-laird-ragni-2019]
* [B. Spector, *Scalar implicatures: exhaustivity and Gricean reasoning* (2007)][spector-2007]
* [S. Mascarenhas, *Formal semantics and the psychology of reasoning* (2014)][mascarenhas-2014]
* [L. Picat, *Inferences with disjunction, interpretation or reasoning?* (2019)][picat-2019]
* [M. Oaksford and N. Chater, *Bayesian Rationality* (2007)][oaksford-chater-2007]
* [V. Crupi, B. Fitelson and K. Tentori, *Probability, confirmation, and the conjunction
  fallacy* (2008)][crupi-fitelson-tentori-2008]
* [K. Tentori, V. Crupi, N. Bonini and D. Osherson, *Comparison of confirmation measures*
  (2007)][tentori-crupi-bonini-osherson-2007]
* [A. Tversky and D. Kahneman, *Extensional Versus Intuitive Reasoning: The Conjunction
  Fallacy in Probability Judgment* (1983)][tversky-kahneman-1983]
* [D. Cummins, *Naive theories and causal deduction* (1995)][cummins-1995]
-/

@[expose] public section

namespace SableMeyerMascarenhas2022

open Set Erotetic Exhaustification MeasureTheory ProbabilityTheory

/-! ### The indirect schema (§2.3, §4) -/

section Schema

variable {W : Type*} {a b c d : Set W}

/-- Experiment 2's schema (10) is the classical schema at `b` with `d` inside the selected
alternative: matching certifies the inside conjunct `d`. -/
theorem exp2_illusory_d (hbd : (b ∩ d).Nonempty) (h : ((c ∩ b) \ d).Nonempty) :
    (disjunction b d c).Illusory (disjunction b d c).Matches d :=
  disjunction_illusory_matches hbd h

/-- In the deterministic limit of the causal link, `d ⊆ a`, the Experiment 2 conclusion `a`
is illusory as well ((10)/(11)); the graded step is the paper's open end. -/
theorem exp2_illusory_a (hda : d ⊆ a) (hbd : (b ∩ d).Nonempty)
    (h : ((c ∩ b) \ a).Nonempty) :
    (disjunction b d c).Illusory (disjunction b d c).Matches a := by
  refine ⟨⟨b ∩ d, by simp [disjunction], fun _ hw ↦ hw.1,
    hbd.elim fun w ⟨hwb, hwd⟩ ↦ ⟨w, ⟨hwb, hwd⟩, hwb⟩, fun _ hw ↦ hda hw.1.2⟩, ?_⟩
  obtain ⟨w, ⟨hwc, hwb⟩, hwa⟩ := h
  exact fun hent ↦ hwa (hent (by simpa using ⟨Or.inr hwc, hwb⟩))

end Schema

/-! ### Mental models and weak necessity (§5.2.1) -/

/-- The three atoms of the schema. -/
inductive Atom
  | a | b | c
  deriving DecidableEq, Fintype

/-- A mental model: a conjunction of literals with gaps, after the paper's rendering of the
revised theory. -/
abbrev MentalModel := Atom → Option Bool

/-- The model with the given literals. -/
def model (xa xb xc : Option Bool) : MentalModel
  | .a => xa
  | .b => xb
  | .c => xc

/-- `m.le m'`: every literal of `m` is a literal of `m'`. -/
def MentalModel.le (m m' : MentalModel) : Prop := ∀ x v, m x = some v → m' x = some v

instance (m m' : MentalModel) : Decidable (m.le m') := by
  unfold MentalModel.le; infer_instance

/-- Weak necessity, as the paper states the revised theory's low-γ System 2: every model of
the conclusion is included in some model of the premises, and some model of the premises
contains no model of the conclusion. -/
def WeakNecessity (Ps C : List MentalModel) : Prop :=
  (∀ m ∈ C, ∃ m' ∈ Ps, m.le m') ∧ ∃ m' ∈ Ps, ∀ m ∈ C, ¬ m.le m'

instance (Ps C : List MentalModel) : Decidable (WeakNecessity Ps C) := by
  unfold WeakNecessity; infer_instance

/-- Strong necessity: every model of the premises includes a model of the conclusion. -/
def StrongNecessity (Ps C : List MentalModel) : Prop := ∀ m' ∈ Ps, ∃ m ∈ C, m.le m'

instance (Ps C : List MentalModel) : Decidable (StrongNecessity Ps C) := by
  unfold StrongNecessity; infer_instance

/-- (12): the two fully explicit models of the premises. -/
def system2Premises : List MentalModel :=
  [model (some true) (some true) (some false), model (some true) (some false) (some true)]

/-- The conclusion consisting of the one positive literal. -/
def concl (x : Atom) : List MentalModel := [fun y ↦ if y = x then some true else none]

/-- §5.2.1: the attractive conclusion `b` and the unattractive `c` are both weak necessities
of (12) — the revised theory's low-γ System 2 cannot see the (13) asymmetry. -/
theorem system2_overgenerates :
    WeakNecessity system2Premises (concl .b) ∧ WeakNecessity system2Premises (concl .c) := by
  decide

/-- Neither conclusion is a strong necessity: high γ resists the fallacy altogether. -/
theorem system2_not_strong :
    ¬ StrongNecessity system2Premises (concl .b) ∧
      ¬ StrongNecessity system2Premises (concl .c) := by
  decide

/-! ### Gaps as negations and the strongly exhaustive reading (§5.2.2) -/

/-- (14): the System-1 models of the premise, with gaps. -/
def system1P1 : List MentalModel :=
  [model (some true) (some true) none, model none none (some true)]

/-- Under model conjunction a gap behaves as a negation: fill it with `false`. -/
def fillGaps (m : MentalModel) : Atom → Bool := fun x ↦ (m x).getD false

/-- (16): filling the gaps makes the System-1 models fully explicit and mutually exclusive. -/
theorem fillGaps_system1P1 :
    system1P1.map fillGaps = [fun x ↦ decide (x ≠ Atom.c), fun x ↦ decide (x = Atom.c)] := by
  simp only [system1P1, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  constructor <;> funext x <;> cases x <;> rfl

/-- Worlds are total assignments. -/
abbrev World := Atom → Bool

instance : MeasurableSpace World := ⊤

/-- The coordinate propositions. -/
def A : Set World := {w | w .a = true}
def B : Set World := {w | w .b = true}
def C : Set World := {w | w .c = true}

instance : DecidablePred (· ∈ A) := fun w ↦ inferInstanceAs (Decidable (w .a = true))
instance : DecidablePred (· ∈ B) := fun w ↦ inferInstanceAs (Decidable (w .b = true))
instance : DecidablePred (· ∈ C) := fun w ↦ inferInstanceAs (Decidable (w .c = true))

/-- §5.2.2: the gaps-as-negations interpretation of the premise is exactly the strongly
exhaustive reading, innocent exclusion against the substitution alternatives. -/
theorem gapNegation_eq_exh :
    exhIE (conjDisjAlternatives A B C) ((A ∩ B) ∪ C) =
      {w | ∃ m ∈ system1P1, w = fillGaps m} := by
  rw [exhIE_conjDisjAlternatives ⟨fillGaps (model (some true) (some true) none), by decide⟩
    ⟨fillGaps (model none none (some true)), by decide⟩]
  ext w
  simp only [system1P1, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  revert w; decide

/-- Under the strongly exhaustive reading the conclusion is valid: [mascarenhas-2014]'s
absolving interpretation. -/
theorem gapNegation_valid : {w | ∃ m ∈ system1P1, w = fillGaps m} ∩ A ⊆ B := by
  rw [← gapNegation_eq_exh,
    exhIE_conjDisjAlternatives ⟨fillGaps (model (some true) (some true) none), by decide⟩
      ⟨fillGaps (model none none (some true)), by decide⟩]
  exact stronglyExhaustive_inter_subset

/-! ### Posteriors and p-validity (§5.3) -/

/-- The premises of the classical schema. -/
abbrev E : Set World := ((A ∩ B) ∪ C) ∩ A

/-- The premises under the exclusive reading: the XOR of the disjuncts. -/
abbrev Exor : Set World := (((A ∩ B) \ C) ∪ (C \ (A ∩ B))) ∩ A

/-- §5.3's "exclusive" reading is the symmetric difference, not the strongly exhaustive
(16). -/
theorem Exor_eq_symmDiff : Exor = symmDiff (A ∩ B) C ∩ A := rfl

/-- Under independent flat priors the posterior of `b` given the premises is 2/3. -/
theorem flat_posterior_b :
    ((uniformOn (univ : Set World))[|E] B).toReal = 2 / 3 := by
  rw [uniformOn_cond finite_univ .of_discrete, univ_inter, ← measureReal_def,
    uniformOn_real_apply]
  have h1 : (E ∩ B).ncard = 2 := by rw [Set.ncard_eq_toFinset_card']; decide
  have h2 : E.ncard = 3 := by rw [Set.ncard_eq_toFinset_card']; decide
  rw [h1, h2]; norm_num

/-- And so is the posterior of the unobserved `c`: the posterior account cannot separate
them. -/
theorem flat_posterior_c :
    ((uniformOn (univ : Set World))[|E] C).toReal = 2 / 3 := by
  rw [uniformOn_cond finite_univ .of_discrete, univ_inter, ← measureReal_def,
    uniformOn_real_apply]
  have h1 : (E ∩ C).ncard = 2 := by rw [Set.ncard_eq_toFinset_card']; decide
  have h2 : E.ncard = 3 := by rw [Set.ncard_eq_toFinset_card']; decide
  rw [h1, h2]; norm_num

/-- The flat prior realizes the symmetry of `Erotetic.posterior_eq_iff`: the two conjunction
priors coincide, so the two posteriors do. -/
theorem flat_posterior_eq :
    (uniformOn (univ : Set World))[B | E] = (uniformOn (univ : Set World))[C | E] := by
  refine (Erotetic.posterior_eq_iff _ .of_discrete ?_).mpr ?_
  · rw [Ne, uniformOn_eq_zero_iff finite_univ, univ_inter]
    exact fun h ↦
      Set.Nonempty.ne_empty ⟨fillGaps (model (some true) (some true) none), by decide⟩ h
  · rw [uniformOn_univ, uniformOn_univ]
    congr 1
    rw [show A ∩ B = ((Finset.univ.filter (· ∈ A ∩ B) : Finset World) : Set World) from by
        ext w; simp,
      show A ∩ C = ((Finset.univ.filter (· ∈ A ∩ C) : Finset World) : Set World) from by
        ext w; simp,
      Measure.count_apply_finset, Measure.count_apply_finset,
      show (Finset.univ.filter (· ∈ A ∩ B)).card = 2 by decide,
      show (Finset.univ.filter (· ∈ A ∩ C)).card = 2 by decide]

/-- Under the exclusive reading both posteriors are 1/2: still no separation. -/
theorem exclusive_posterior :
    ((uniformOn (univ : Set World))[|Exor] B).toReal = 1 / 2 ∧
      ((uniformOn (univ : Set World))[|Exor] C).toReal = 1 / 2 := by
  rw [uniformOn_cond finite_univ .of_discrete, univ_inter, ← measureReal_def,
    ← measureReal_def, uniformOn_real_apply, uniformOn_real_apply]
  have h1 : (Exor ∩ B).ncard = 1 := by rw [Set.ncard_eq_toFinset_card']; decide
  have h2 : (Exor ∩ C).ncard = 1 := by rw [Set.ncard_eq_toFinset_card']; decide
  have h3 : Exor.ncard = 2 := by rw [Set.ncard_eq_toFinset_card']; decide
  rw [h1, h2, h3]; norm_num

/-- p-validity: the conclusion is at least as probable as the premises under every
probability distribution. -/
def PValid (E q : Set World) : Prop :=
  ∀ μ : Measure World, IsProbabilityMeasure μ → μ E ≤ μ q

/-- The paper's counterexample distribution: uniform on the two mutually exclusive worlds. -/
def witness : Set World :=
  {fillGaps (model (some true) (some true) none), fillGaps (model (some true) none (some true))}

theorem witness_finite : witness.Finite := Set.toFinite _

theorem witness_nonempty : witness.Nonempty := ⟨_, Or.inl rfl⟩

theorem not_pValid_of {E q : Set World} (hE : witness ⊆ E) (hq : ¬ witness ⊆ q) :
    ¬ PValid E q := fun h ↦ by
  have hp := isProbabilityMeasure_uniformOn witness_finite witness_nonempty
  have h1 := h _ hp
  rw [uniformOn_eq_one_of witness_finite witness_nonempty hE] at h1
  exact hq ((uniformOn_eq_one_iff witness_finite witness_nonempty).1
    (le_antisymm prob_le_one h1))

/-- Neither conclusion is p-valid, under either reading of the disjunction (§5.3, fn 1). -/
theorem not_pValid :
    ¬ PValid E B ∧ ¬ PValid E C ∧ ¬ PValid Exor B ∧ ¬ PValid Exor C := by
  refine ⟨not_pValid_of ?_ ?_, not_pValid_of ?_ ?_, not_pValid_of ?_ ?_, not_pValid_of ?_ ?_⟩
  · rintro w (rfl | rfl) <;> decide
  · exact fun h ↦ absurd (h (Or.inr rfl)) (by decide)
  · rintro w (rfl | rfl) <;> decide
  · exact fun h ↦ absurd (h (Or.inl rfl)) (by decide)
  · rintro w (rfl | rfl) <;> decide
  · exact fun h ↦ absurd (h (Or.inr rfl)) (by decide)
  · rintro w (rfl | rfl) <;> decide
  · exact fun h ↦ absurd (h (Or.inl rfl)) (by decide)

/-! ### Confirmation and selection (§5.4) -/

section Confirmation

variable {W : Type*} [MeasurableSpace W] (μ : Measure W)

/-- The Difference measure of confirmation, `D(h, e) = P(h|e) − P(h)`
[crupi-fitelson-tentori-2008]. -/
noncomputable def confirmationD (h e : Set W) : ℝ := (μ[|e] h).toReal - (μ h).toReal

variable {μ} {a b c d f : Set W}

/-- `D(a ∧ b, d) = P(b) · D(a, d)` when `b` is independent of `a` and of `a ∧ d`: the
supplement's identity behind the §5.4 asymmetry. -/
theorem confirmationD_inter_eq_mul (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) :
    confirmationD μ (a ∩ b) d = (μ b).toReal * confirmationD μ a d := by
  have h1 : μ (d ∩ (a ∩ b)) = μ (d ∩ a) * μ b := by
    rw [inter_comm d a, ← hadb.measure_inter_eq_mul]; congr 1; ext; simp; tauto
  simp only [confirmationD, cond_real_apply μ hd, h1, hab.measure_inter_eq_mul,
    ENNReal.toReal_mul]
  ring

/-- `D(c, d) = 0` when `c` and `d` are independent: the hint is orthogonal to the second
disjunct. -/
theorem confirmationD_eq_zero (hd : MeasurableSet d) (hcd : IndepSet c d μ) (h0 : μ d ≠ 0)
    (hT : μ d ≠ ⊤) : confirmationD μ c d = 0 := by
  have h1 : μ (d ∩ c) = μ d * μ c := by rw [inter_comm, hcd.measure_inter_eq_mul, mul_comm]
  have h2 : (μ d).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, hT⟩
  rw [confirmationD, cond_real_apply μ hd, h1, ENNReal.toReal_mul, mul_comm, mul_div_assoc,
    div_self h2, mul_one, sub_self]

/-- The §5.4 asymmetry: a hint that confirms `a` confirms the conjunction `a ∧ b`. -/
theorem confirmationD_inter_pos (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) (hb : 0 < (μ b).toReal) (ha : 0 < confirmationD μ a d) :
    0 < confirmationD μ (a ∩ b) d := by
  rw [confirmationD_inter_eq_mul hd hab hadb]; exact mul_pos hb ha

variable (μ) in
/-- Selection by confirmation: the alternative whose probability the hint raises most. -/
def BestConfirmed (P : Problem W) (p : Set W) : Prop :=
  ∀ p' ∈ P.alts, p' ≠ p → confirmationD μ p' P.hint < confirmationD μ p P.hint

/-- In the indirect schema the first alternative is uniquely selected by confirmation. -/
theorem indirect_bestConfirmed (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) (hcd : IndepSet c d μ) (h0 : μ d ≠ 0) (hT : μ d ≠ ⊤)
    (hb : 0 < (μ b).toReal) (ha : 0 < confirmationD μ a d) :
    BestConfirmed μ (indirect a b c d) (a ∩ b) := by
  rintro p' hp' hne
  simp only [indirect, mem_insert_iff, mem_singleton_iff] at hp'
  rcases hp' with rfl | rfl
  · exact (hne rfl).elim
  · show confirmationD μ p' d < confirmationD μ (a ∩ b) d
    rw [confirmationD_eq_zero hd hcd h0 hT]
    exact confirmationD_inter_pos hd hab hadb hb ha

/-- The indirect illusion under selection by confirmation: the positive witness through the
whole pipeline. -/
theorem indirect_illusory_bestConfirmed (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) (hcd : IndepSet c d μ) (h0 : μ d ≠ 0) (hT : μ d ≠ ⊤)
    (hb : 0 < (μ b).toReal) (ha : 0 < confirmationD μ a d) (hne : (a ∩ b ∩ d).Nonempty)
    (h : ((c ∩ d) \ b).Nonempty) :
    (indirect a b c d).Illusory (BestConfirmed μ (indirect a b c d)) b :=
  indirect_illusory (indirect_bestConfirmed hd hab hadb hcd h0 hT hb ha) hne h

/-- The second disjunct is never selected: the (13) asymmetry at the selection step. -/
theorem not_bestConfirmed_right (hd : MeasurableSet d) (hab : IndepSet a b μ)
    (hadb : IndepSet (a ∩ d) b μ) (hcd : IndepSet c d μ) (h0 : μ d ≠ 0) (hT : μ d ≠ ⊤)
    (hb : 0 < (μ b).toReal) (ha : 0 < confirmationD μ a d) (hne : a ∩ b ≠ c) :
    ¬ BestConfirmed μ (indirect a b c d) c := fun h ↦
  lt_asymm
    (indirect_bestConfirmed hd hab hadb hcd h0 hT hb ha c (by simp [indirect]) hne.symm)
    (h (a ∩ b) (by simp [indirect]) hne)

/-- (18): the conjunction fallacy is the indirect schema at the options `(f ∧ b) ∨ b`. -/
def conjunctionFallacy (f b d : Set W) : Problem W := indirect f b b d

/-- The description selects the conjunctive option: the same lemma, instantiated. -/
theorem conjunctionFallacy_bestConfirmed (hd : MeasurableSet d) (hfb : IndepSet f b μ)
    (hfdb : IndepSet (f ∩ d) b μ) (hbd : IndepSet b d μ) (h0 : μ d ≠ 0) (hT : μ d ≠ ⊤)
    (hb : 0 < (μ b).toReal) (hf : 0 < confirmationD μ f d) :
    BestConfirmed μ (conjunctionFallacy f b d) (f ∩ b) :=
  indirect_bestConfirmed hd hfb hfdb hbd h0 hT hb hf

end Confirmation

/-! ### The experiments (§3, §4) -/

/-- Seven of the eight item sets survived the norming analysis, the number of targets each
participant saw. -/
theorem items_kept_card :
    (Finset.univ.filter fun i ↦ (items i).status = ItemStatus.kept).card =
      targetsPerParticipant := by
  decide

/-- §5: in the matching limit `P(a|d) = 1`, the printed Experiment 1 model predicts the
literature's acceptance: intercept plus slope is the printed 0.92. -/
theorem matching_limit :
    ((regressions .experimentOne).intercept.getD ⟨0, 0⟩).toRat +
      (regressions .experimentOne).slope.toRat = matchingLimitAcceptance.toRat := by
  simp [regressions, matchingLimitAcceptance, Data.Experiments.Decimal.toRat]
  norm_num

end SableMeyerMascarenhas2022
