import Linglib.Pragmatics.RSA.Uniform

/-!
# Champollion, Alsop & Grosu (2019): free choice disjunction as a rational speech act

Free choice — *You may take an apple or a pear* conveys that each fruit may be taken by
itself — does not follow from modal logic, and a speaker who prefers informative utterances
never has reason to choose the disjunction over a disjunct. The paper adds semantic
uncertainty: two interpretation functions, the classical (6) and the exhaustified (7), over
which the pragmatic listener reasons jointly with states and utterances (8). Under the
exhaustified function a bare disjunct risks the reading *only that fruit*, so at the
free-choice states Only One and Any Number the disjunction is the speaker's safe choice
(`speaker_or_onlyOne_exh`, `speaker_prefers_a_at_onlyA_exh`), and the listener inverts the
avoidance: hearing *or*, each free-choice state outweighs each other state at the paper's
α = 100 (`fci_derived`, Table 5), and the free-choice states already carry the majority at
α = 2 (`fci_majority_low_alpha`).

Exclusivity — not both — tracks the prior instead: under a prior favouring Any Number the
listener hearing *or* ranks Any Number above every other state, at every rationality
(`anyNumber_of_prior`, Table 6) — the paper's account of why exclusivity, unlike free
choice, is cancelable. Under negation the negated disjunction is unambiguous and maximally
strong, so the listener assigns no mass to the states at which free choice would survive
(`no_fci_under_negation`, Table 9). The variants without the conjunctive alternative
(Tables 7–8) are not formalized.

## References

* [champollion-alsop-grosu-2019]
* [franke-2011]
* [fox-2007]
* [bergen-levy-goodman-2016]
* [frank-goodman-2012]
* [kratzer-shimoyama-2002]
* [simons-2005]
-/

namespace ChampollionAlsopGrosu2019

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### States, utterances, interpretation functions (Table 2, (5)–(7)) -/

/-- Permission states (Table 2): Franke's All True split into Any Number and Only Both. -/
inductive FCState where
  | onlyA | onlyB | onlyOne | anyNumber | onlyBoth
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace FCState := ⊤
instance : DiscreteMeasurableSpace FCState := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass FCState := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The four utterances (5). -/
inductive Utterance where
  | a | b | or_ | and_
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass Utterance := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The interpretation functions: classical modal logic and its exhaustification. -/
inductive Interp where
  | literal | exhaustified
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Interp := ⊤
instance : DiscreteMeasurableSpace Interp := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass Interp := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Free choice: each fruit may be taken by itself. -/
def HasFCI : FCState → Prop
  | .onlyOne | .anyNumber => True
  | _ => False

instance : DecidablePred HasFCI
  | .onlyA | .onlyB | .onlyBoth => .isFalse id
  | .onlyOne | .anyNumber => .isTrue trivial

/-- Interpretation function 1 (6): classical modal logic. -/
def I1 : Utterance → FCState → Prop
  | .a, .onlyB => False
  | .a, _ => True
  | .b, .onlyA => False
  | .b, _ => True
  | .or_, _ => True
  | .and_, .anyNumber | .and_, .onlyBoth => True
  | .and_, _ => False

instance : ∀ u, DecidablePred (I1 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- Interpretation function 2 (7): the exhaustified meanings. -/
def I2 : Utterance → FCState → Prop
  | .a, .onlyA => True
  | .a, _ => False
  | .b, .onlyB => True
  | .b, _ => False
  | .or_, .onlyBoth => False
  | .or_, _ => True
  | .and_, .onlyBoth => True
  | .and_, _ => False

instance : ∀ u, DecidablePred (I2 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- Meaning indexed by interpretation function. -/
def interpMeaning : Interp → Utterance → FCState → Prop
  | .literal => I1
  | .exhaustified => I2

instance : ∀ i u, DecidablePred (interpMeaning i u)
  | .literal, u => inferInstanceAs (DecidablePred (I1 u))
  | .exhaustified, u => inferInstanceAs (DecidablePred (I2 u))

/-- The extension of each utterance under each interpretation function. -/
def sem (i : Interp) (u : Utterance) : Finset FCState := Finset.univ.filter (interpMeaning i u)

@[simp] theorem mem_sem {i : Interp} {u : Utterance} {w : FCState} :
    w ∈ sem i u ↔ interpMeaning i u w := by simp [sem]

/-- Every state is truthfully describable under every interpretation function. -/
theorem expressible : ∀ i w, ∃ u, w ∈ sem i u := by decide

/-- Exhaustification only strengthens. -/
theorem I2_refines_I1 : ∀ u w, I2 u w → I1 u w := by decide

/-- The classical disjunction is true everywhere — maximally uninformative. -/
theorem I1_or_everywhere : ∀ w, I1 .or_ w := by decide

/-- The exhaustified disjunction excludes exactly Only Both. -/
theorem I2_or_excludes_onlyBoth : ∀ w, I2 .or_ w ↔ w ≠ .onlyBoth := by decide

/-- The exhaustified disjunct singles out exactly Only A — the risk the speaker avoids. -/
theorem I2_a_singleton : ∀ w, I2 .a w ↔ w = .onlyA := by decide

/-! ### The model (8) at a uniform prior -/

/-- The speaker under a fixed interpretation function (8b). -/
noncomputable abbrev speaker (i : Interp) (α : ℝ) : Kernel FCState Utterance :=
  uniformSpeaker (sem i) α

/-- The pragmatic listener (8c): the Bayesian inverse of the interpretation-indexed speaker
at a uniform prior over states and interpretation functions; `.fst` marginalizes over the
interpretation. -/
noncomputable abbrev listener (α : ℝ) : Kernel Utterance (FCState × Interp) :=
  familyListener (fun i => uniformListener (sem i)) α 1 (uniformOn Set.univ)

/-- Under the exhaustified function at Only One, *or* is the only true utterance, so the
speaker produces it with certainty at every rationality (§3.3). -/
theorem speaker_or_onlyOne_exh {α : ℝ} (hα : 0 < α) :
    speaker .exhaustified α .onlyOne {.or_} = 1 :=
  uniformSpeaker_apply_singleton_eq_one _ hα (by decide) (by decide)

/-- Under the exhaustified function at Any Number, *or* is the only true utterance. -/
theorem speaker_or_anyNumber_exh {α : ℝ} (hα : 0 < α) :
    speaker .exhaustified α .anyNumber {.or_} = 1 :=
  uniformSpeaker_apply_singleton_eq_one _ hα (by decide) (by decide)

/-- Under the exhaustified function at Only Both, *or* is false. -/
theorem speaker_or_onlyBoth_exh {α : ℝ} (hα : 0 < α) :
    speaker .exhaustified α .onlyBoth {.or_} = 0 :=
  uniformSpeaker_apply_singleton_eq_zero _ hα (by decide)

/-- The avoidance mechanism at the speaker: under the exhaustified function at Only A the
bare disjunct beats the disjunction at every rationality. -/
theorem speaker_prefers_a_at_onlyA_exh {α : ℝ} (hα : 0 < α) :
    (speaker .exhaustified α .onlyA).real {.or_} < (speaker .exhaustified α .onlyA).real {.a} :=
  uniformSpeaker_real_singleton_lt_of_card_lt _ hα (by decide) (by decide) (by decide)

/-- **Free choice derived** (Table 5): hearing *or* at the paper's α = 100, the listener
ranks each free-choice state — Only One and Any Number, the paper's 0.5 each — above each
of Only A, Only B, and Only Both (each ≈ 0). -/
theorem fci_derived :
    ∀ w ∈ ({.onlyA, .onlyB, .onlyBoth} : Finset FCState),
      ∀ w' ∈ ({.onlyOne, .anyNumber} : Finset FCState),
        (listener 100 .or_).fst.real {w} < (listener 100 .or_).fst.real {w'} := by
  intro w hw w' hw'
  rw [Measure.fst_real_singleton, Measure.fst_real_singleton]
  fin_cases hw <;> fin_cases hw' <;>
    exact familyListener_uniform_real_lt_of_divPowSum sem expressible (k := 100) (D := 20)
      (by decide +kernel) (by decide +kernel)

/-- The free-choice pairs of the joint listener. -/
def fciPairs : Finset (FCState × Interp) := Finset.univ.filter fun p => HasFCI p.1

/-- The remaining pairs. -/
def nonFciPairs : Finset (FCState × Interp) := Finset.univ.filter fun p => ¬ HasFCI p.1

/-- At α = 2 the free-choice states still carry the majority of the posterior given *or*
(the paper's "only 70%"). -/
theorem fci_majority_low_alpha :
    (listener 2 .or_).real ↑nonFciPairs < (listener 2 .or_).real ↑fciPairs :=
  familyListener_uniform_real_lt_of_divPowSum sem expressible (k := 2) (D := 20)
    (by decide +kernel) (by decide +kernel)

/-! ### Prior sensitivity (Table 6)

The prior enters the literal listener (8a) and the pragmatic listener (8c) alike. -/

/-- Prior weights favouring Any Number: 12 against 1 for each other state (75%). -/
def biasedWeight : FCState → ℕ
  | .anyNumber => 12
  | _ => 1

/-- The state prior. -/
noncomputable def priorB : Measure FCState := ∑ w, (biasedWeight w : ℝ≥0∞) • Measure.dirac w

/-- The joint prior, the interpretation function drawn uniformly. -/
noncomputable def jointPriorB : Measure (FCState × Interp) :=
  ∑ p, (biasedWeight p.1 : ℝ≥0∞) • Measure.dirac p

theorem priorB_singleton (w : FCState) : priorB {w} = biasedWeight w :=
  Measure.sum_smul_dirac_apply_singleton (fun w => (biasedWeight w : ℝ≥0∞)) w

theorem jointPriorB_singleton (p : FCState × Interp) : jointPriorB {p} = biasedWeight p.1 :=
  Measure.sum_smul_dirac_apply_singleton (fun p : FCState × Interp => (biasedWeight p.1 : ℝ≥0∞)) p

instance : IsFiniteMeasure priorB :=
  ⟨by
    rw [priorB, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun w _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.natCast_lt_top _⟩

instance : IsFiniteMeasure jointPriorB :=
  ⟨by
    rw [jointPriorB, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun p _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.natCast_lt_top _⟩

/-- The extensions as sets. -/
def semSet (i : Interp) (u : Utterance) : Set FCState := ↑(sem i u)

/-- The literal listeners at the biased prior (8a). -/
noncomputable def famB (i : Interp) : Kernel Utterance FCState :=
  literalListener priorB fun u => (semSet i u).indicator 1

/-- The pragmatic listener at the biased prior. -/
noncomputable def listenerB (α : ℝ) : Kernel Utterance (FCState × Interp) :=
  familyListener famB α 1 jointPriorB

theorem jointPriorB_real_singleton (p : FCState × Interp) :
    jointPriorB.real {p} = biasedWeight p.1 := by
  rw [measureReal_def, jointPriorB_singleton, ENNReal.toReal_natCast]

/-- **Exclusivity tracks the prior** (Table 6): with 75% of the prior on Any Number, the
listener hearing *or* ranks Any Number above every other state at every rationality —
under the exhaustified function *or* is produced there with certainty, and no other state
has a comparable prior. -/
theorem anyNumber_of_prior {α : ℝ} (hα : 0 < α) (w : FCState) (hw : w ≠ .anyNumber) :
    (listenerB α .or_).fst.real {w} < (listenerB α .or_).fst.real {.anyNumber} := by
  have hone : RSA.speaker α 1 (famB .exhaustified) .anyNumber {.or_} = 1 :=
    speaker_apply_singleton_eq_one (L := famB .exhaustified) (cost := 1) hα one_ne_zero
      ENNReal.one_ne_top
      (by
        have hL : famB .exhaustified .or_ {.anyNumber}
            = (priorB (semSet .exhaustified .or_))⁻¹ * priorB {.anyNumber} :=
          literalListener_indicator_apply_singleton priorB (semSet .exhaustified)
            (Finset.mem_coe.mpr (by decide))
        rw [hL]
        exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
          (by rw [priorB_singleton]; simp [biasedWeight]))
      (literalListener_indicator_apply_singleton_le_one (sem := semSet .exhaustified)
        (u := .or_) _ (measure_ne_top _ _) (Finset.mem_coe.mpr (by decide)))
      fun u' hu' => literalListener_indicator_apply_singleton_of_notMem
        (sem := semSet .exhaustified) _ fun h =>
          absurd (Finset.mem_coe.mp h) (by revert hu'; cases u' <;> decide)
  have hu : (familySpeaker famB α 1 ∘ₘ jointPriorB) {.or_} ≠ 0 :=
    comp_familySpeaker_ne_zero (w := .anyNumber) (l := .exhaustified)
      (by rw [jointPriorB_singleton]; simp [biasedWeight]) (by rw [hone]; exact one_ne_zero)
  rw [Measure.fst_real_singleton, Measure.fst_real_singleton, listenerB,
    familyListener_real_lt_iff _ _ _ hu, Finset.sum_product, Finset.sum_product,
    Finset.sum_singleton, Finset.sum_singleton,
    show (Finset.univ : Finset Interp) = {.literal, .exhaustified} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_singleton, jointPriorB_real_singleton, jointPriorB_real_singleton,
    jointPriorB_real_singleton, jointPriorB_real_singleton]
  have h1 := speaker_real_singleton_le_one α 1 (famB .literal) w .or_
  have h2 := speaker_real_singleton_le_one α 1 (famB .exhaustified) w .or_
  have h3 : (RSA.speaker α 1 (famB .exhaustified) .anyNumber).real {.or_} = 1 := by
    rw [measureReal_def, hone, ENNReal.toReal_one]
  have h4 := measureReal_nonneg (μ := RSA.speaker α 1 (famB .literal) .anyNumber) (s := {.or_})
  have hw1 : (biasedWeight w : ℝ) = 1 := by cases w <;> simp_all [biasedWeight]
  rw [h3, hw1]
  simp only [biasedWeight]
  push_cast
  linarith

/-! ### No free choice under negation (§4, Table 9) -/

/-- The states of the negation model. -/
inductive NegState where
  | onlyA | onlyB | onlyOne | neither
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace NegState := ⊤
instance : DiscreteMeasurableSpace NegState := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass NegState := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The negated utterances (10). -/
inductive NegUtterance where
  | notA | notB | notOr | notAnd
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace NegUtterance := ⊤
instance : DiscreteMeasurableSpace NegUtterance := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass NegUtterance :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Interpretation function 1 under negation (11). -/
def N1 : NegUtterance → NegState → Prop
  | .notA, .onlyB | .notA, .neither => True
  | .notA, _ => False
  | .notB, .onlyA | .notB, .neither => True
  | .notB, _ => False
  | .notOr, .neither => True
  | .notOr, _ => False
  | .notAnd, _ => True

/-- Interpretation function 2 under negation (12): weakened, not strengthened. -/
def N2 : NegUtterance → NegState → Prop
  | .notA, .onlyA => False
  | .notA, _ => True
  | .notB, .onlyB => False
  | .notB, _ => True
  | .notOr, .neither => True
  | .notOr, _ => False
  | .notAnd, _ => True

instance : ∀ u, DecidablePred (N1 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

instance : ∀ u, DecidablePred (N2 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- The negated meanings indexed by interpretation function. -/
def negMeaning : Interp → NegUtterance → NegState → Prop
  | .literal => N1
  | .exhaustified => N2

instance : ∀ i u, DecidablePred (negMeaning i u)
  | .literal, u => inferInstanceAs (DecidablePred (N1 u))
  | .exhaustified, u => inferInstanceAs (DecidablePred (N2 u))

/-- The extensions of the negation model. -/
def negSem (i : Interp) (u : NegUtterance) : Finset NegState :=
  Finset.univ.filter (negMeaning i u)

@[simp] theorem mem_negSem {i : Interp} {u : NegUtterance} {w : NegState} :
    w ∈ negSem i u ↔ negMeaning i u w := by simp [negSem]

/-- The negated disjunction is unambiguous: true exactly at Neither under both functions. -/
theorem negSem_notOr : ∀ i, negSem i .notOr = {.neither} := by decide

/-- The listener of the negation model. -/
noncomputable abbrev negListener (α : ℝ) : Kernel NegUtterance (NegState × Interp) :=
  familyListener (fun i => uniformListener (negSem i)) α 1 (uniformOn Set.univ)

/-- **No free choice under negation** (Table 9): hearing *you may not take an apple or a
pear*, the listener assigns no mass to any state other than Neither — in particular none to
Only A and Only B, where a free-choice reading of the negated disjunction would be true. -/
theorem no_fci_under_negation {α : ℝ} (hα : 0 < α) {p : NegState × Interp}
    (hp : p.1 ≠ .neither) : negListener α .notOr {p} = 0 :=
  familyListener_uniform_apply_singleton_eq_zero negSem hα ⟨.literal, .neither, by decide⟩
    (by rw [negSem_notOr, Finset.mem_singleton]; exact hp)

end ChampollionAlsopGrosu2019
