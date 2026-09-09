import Linglib.Logic.Modal.Defs
import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Quantification.Properties
import Linglib.Data.Examples.GeurtsPouscoulous2009

/-!
# Geurts and Pouscoulous (2009): Embedded implicatures?!?

This file formalizes the theoretical frame of [geurts-pouscoulous-2009]'s experimental case
against conventionalist theories of scalar implicature ([chierchia-2004], [fox-2007],
[chierchia-fox-spector-2008]), which posit a silent exhaustivity operator adjoinable to any
clause and predict local scalar inferences systematically. The operator `so` negates every
stronger alternative of its prejacent; under a belief verb the parse with `so` below the verb
yields the local reading, that the agent believes *some but not all*, and the parse above it the
global reading, that the agent believes *some* and does not believe *all*
(`local_reading`, `so_pair`). The paper's Gricean reply is that the local reading follows from the
global one whenever the agent is opinionated on the stronger alternative
(`local_of_global_of_opinionated`), while the analogous derivation for a universal quantifier
needs a uniformity assumption across the domain (`all_not_all_of_uniform`) that is far less
plausible, so seemingly local inferences are expected under *believe* and nowhere else.

Mainstream conventionalism predicts the local construal wherever the embedding scope is not
downward entailing (`PredictsLocalSI`, weakly `PredictsLocalSIWeak`). The third experiment's
verification items are reconstructed as situations in which the classical and the local construal
of each sentence conflict (`rows_construals_conflict`); participants answered by the classical
construal throughout (`rows_observed_classical`), against the prediction derived from the scope
monotonicity of the five quantifiers (`rows_predicted_mainstream`).

## Implementation notes

* The experiments' response rates (Tables 2–5) are recorded as features of the rows, with the
  verification and bracketed prediction rates turned into majority responses; the paper's
  statistical tests and its methodological argument that the inference paradigm inflates rates
  stay in prose.
* The verification situations are three squares and three circles; the exact figures of the
  stimuli are not given in the paper, only the conditions they satisfy, which the three situations
  here meet.
* The paper's remark that lexicalist conventionalism reaches only the local reading is not
  formalized; `so` is the syntax-based variant's operator.

## References

* [geurts-pouscoulous-2009]
* [chierchia-2004]
* [fox-2007]
* [chierchia-fox-spector-2008]
* [sauerland-2004]
-/

namespace GeurtsPouscoulous2009

open Quantification ModalLogic Data.Examples

variable {W : Type*}

/-! ### The silent exhaustivity operator -/

/-- The silent operator of syntax-based conventionalism: the prejacent with every stronger
alternative negated. -/
def so (φ : Set W) (A : Set (Set W)) : Set W := {w | w ∈ φ ∧ ∀ ψ ∈ A, ψ ⊂ φ → w ∉ ψ}

/-- Against the two-membered scale of *some* and *all*, the operator returns *some but not all*. -/
theorem so_pair {φ ψ : Set W} (h : ψ ⊂ φ) : so φ {φ, ψ} = φ \ ψ := by
  ext w
  simp only [so, Set.mem_ofPred_eq, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  exact ⟨λ ⟨hw, _, hψ⟩ => ⟨hw, hψ h⟩,
    λ ⟨hw, hψ⟩ => ⟨hw, λ hφ => absurd hφ (lt_irrefl φ), λ _ => hψ⟩⟩

/-- The parse with the operator below the belief verb: the agent believes *some* and believes
*not all*. -/
theorem local_reading (R : W → W → Prop) {some all : Set W} (h : all ⊂ some) :
    box R (so some {some, all}) = λ w => box R some w ∧ box R allᶜ w := by
  rw [so_pair h]
  funext w
  exact propext ⟨λ hb => ⟨λ v hv => (hb v hv).1, λ v hv => (hb v hv).2⟩,
    λ ⟨h₁, h₂⟩ v hv => ⟨h₁ v hv, h₂ v hv⟩⟩

/-- The Gricean derivation of a seemingly local inference: the parse with the operator above the
belief verb says the agent believes *some* and does not believe *all*, and an agent opinionated on
*all* then believes *not all*, which is the local reading. -/
theorem local_of_global_of_opinionated (R : W → W → Prop) {some all : Set W} (h : all ⊂ some)
    {w : W} (h₃₁ : box R some w) (h₃₂ : ¬ box R all w) (h₃₃ : box R all w ∨ box R allᶜ w) :
    box R (so some {some, all}) w := by
  rw [local_reading R h]
  exact ⟨h₃₁, h₃₃.resolve_left h₃₂⟩

/-- The same derivation for a universal quantifier: the global implicature that not every
customer shot at every salesman yields that none did only under the uniformity assumption that
either all or none did. -/
theorem all_not_all_of_uniform {C S : Type*} (Shot : C → S → Prop) (h₃₆ : ¬ ∀ c s, Shot c s)
    (h₃₈ : (∀ c s, Shot c s) ∨ ∀ c, ¬ ∀ s, Shot c s) : ∀ c, ¬ ∀ s, Shot c s :=
  h₃₈.resolve_left h₃₆

/-! ### Monotonicity and the mainstream prediction -/

variable {α : Type*}

/-- The stronger mainstream prediction: a local scalar inference is preferred in every scope that
is not downward entailing. -/
def PredictsLocalSI (Q : GQ α) : Prop := ¬ ScopeDownwardMono Q

/-- The weaker prediction: a local scalar inference is preferred in upward-entailing scopes. -/
def PredictsLocalSIWeak (Q : GQ α) : Prop := ScopeUpwardMono Q

/-- The quantifiers over squares of the third experiment's sentences. -/
inductive Quant
  | all | moreThanOne | exactlyTwo | notAll | notMoreThanOne
  deriving DecidableEq, Repr

noncomputable def Quant.sem [Fintype α] : Quant → GQ α
  | .all => every_sem
  | .moreThanOne => at_least_n_sem 2
  | .exactlyTwo => exactly_n_sem 2
  | .notAll => outerNeg every_sem
  | .notMoreThanOne => at_most_n_sem 1

theorem all_predictsLocalSIWeak [Fintype α] : PredictsLocalSIWeak (Quant.all.sem : GQ α) :=
  every_scope_up

theorem moreThanOne_predictsLocalSIWeak [Fintype α] :
    PredictsLocalSIWeak (Quant.moreThanOne.sem : GQ α) :=
  at_least_n_scope_up 2

theorem notAll_not_predictsLocalSI [Fintype α] : ¬ PredictsLocalSI (Quant.notAll.sem : GQ α) :=
  not_not.mpr (outerNeg_up_to_down _ every_scope_up)

theorem notMoreThanOne_not_predictsLocalSI [Fintype α] :
    ¬ PredictsLocalSI (Quant.notMoreThanOne.sem : GQ α) :=
  not_not.mpr (at_most_n_scope_down 1)

/-! ### The verification situations -/

/-- A situation of the third experiment: which squares are connected with which circles. -/
abbrev Situation := Fin 3 → Fin 3 → Prop

/-- Every square connected with some circle and two of them with all: the situation for *all*,
*more than one* and the two downward-entailing sentences. -/
abbrev allSome : Situation := λ s c => s ≠ 0 ∨ c = 0

/-- One square connected with some but not all circles, one with all, one with none. -/
abbrev onePartial : Situation := λ s c => s = 1 ∨ (s = 0 ∧ c = 0)

/-- Two squares connected with some but not all circles, one with all. -/
abbrev twoPartial : Situation := λ s c => s = 2 ∨ c = 0

/-- *Connected with some of the circles*. -/
abbrev someC (R : Situation) (s : Fin 3) : Prop := ∃ c, R s c

/-- The local construal, *connected with some but not all of the circles*. -/
abbrev someNotAllC (R : Situation) (s : Fin 3) : Prop := (∃ c, R s c) ∧ ¬ ∀ c, R s c

/-- The two verification trials of *exactly two*; the other sentences had one. -/
inductive Trial
  | none | a | b
  deriving DecidableEq, Repr

def situation : Quant → Trial → Situation
  | .exactlyTwo, .a => onePartial
  | .exactlyTwo, .b => twoPartial
  | _, _ => allSome

/-- The classical construal of a verification item. -/
def Classical (q : Quant) (t : Trial) : Prop := q.sem (λ _ => True) (someC (situation q t))

/-- The local-implicature construal of a verification item. -/
def Local (q : Quant) (t : Trial) : Prop := q.sem (λ _ => True) (someNotAllC (situation q t))

/-- What mainstream conventionalism predicts of an item: the local construal outside
downward-entailing scopes, the classical one within them. -/
def Mainstream (q : Quant) (t : Trial) : Prop :=
  (PredictsLocalSI (q.sem : GQ (Fin 3)) ∧ Local q t) ∨
    (¬ PredictsLocalSI (q.sem : GQ (Fin 3)) ∧ Classical q t)

theorem all_predictsLocalSI : PredictsLocalSI (Quant.all.sem : GQ (Fin 3)) := λ h =>
  h (λ _ => True) (λ _ => False) (λ _ => True) (λ _ hf => hf.elim) (λ _ _ => trivial) 0 trivial

theorem moreThanOne_predictsLocalSI : PredictsLocalSI (Quant.moreThanOne.sem : GQ (Fin 3)) := by
  intro h
  have key := h (λ _ => True) (λ _ => False) (λ _ => True) (λ _ hf => hf.elim)
  simp only [Quant.sem, at_least_n_sem] at key
  rw [count_eq_decidable (λ _ : Fin 3 => True ∧ True),
    count_eq_decidable (λ _ : Fin 3 => True ∧ False)] at key
  revert key
  decide

theorem exactlyTwo_predictsLocalSI : PredictsLocalSI (Quant.exactlyTwo.sem : GQ (Fin 3)) := by
  intro h
  have key := h (λ _ => True) (· = 0) (λ s => s = 0 ∨ s = 1) (λ _ hs => Or.inl hs)
  simp only [Quant.sem, exactly_n_sem] at key
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ (s = 0 ∨ s = 1)),
    count_eq_decidable (λ s : Fin 3 => True ∧ s = 0)] at key
  revert key
  decide

theorem classical_all : Classical .all .none :=
  show ∀ s : Fin 3, True → someC allSome s by decide

theorem not_local_all : ¬ Local .all .none :=
  show ¬ ∀ s : Fin 3, True → someNotAllC allSome s by decide

theorem classical_moreThanOne : Classical .moreThanOne .none := by
  simp only [Classical, Quant.sem, situation, at_least_n_sem]
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ someC allSome s)]
  decide

theorem not_local_moreThanOne : ¬ Local .moreThanOne .none := by
  simp only [Local, Quant.sem, situation, at_least_n_sem]
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ someNotAllC allSome s)]
  decide

theorem classical_exactlyTwo_a : Classical .exactlyTwo .a := by
  simp only [Classical, Quant.sem, situation, exactly_n_sem]
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ someC onePartial s)]
  decide

theorem not_local_exactlyTwo_a : ¬ Local .exactlyTwo .a := by
  simp only [Local, Quant.sem, situation, exactly_n_sem]
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ someNotAllC onePartial s)]
  decide

theorem not_classical_exactlyTwo_b : ¬ Classical .exactlyTwo .b := by
  simp only [Classical, Quant.sem, situation, exactly_n_sem]
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ someC twoPartial s)]
  decide

theorem local_exactlyTwo_b : Local .exactlyTwo .b := by
  simp only [Local, Quant.sem, situation, exactly_n_sem]
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ someNotAllC twoPartial s)]
  decide

theorem not_classical_notAll : ¬ Classical .notAll .none :=
  show ¬ ¬ ∀ s : Fin 3, True → someC allSome s by decide

theorem local_notAll : Local .notAll .none :=
  show ¬ ∀ s : Fin 3, True → someNotAllC allSome s by decide

theorem not_classical_notMoreThanOne : ¬ Classical .notMoreThanOne .none := by
  simp only [Classical, Quant.sem, situation, at_most_n_sem]
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ someC allSome s)]
  decide

theorem local_notMoreThanOne : Local .notMoreThanOne .none := by
  simp only [Local, Quant.sem, situation, at_most_n_sem]
  rw [count_eq_decidable (λ s : Fin 3 => True ∧ someNotAllC allSome s)]
  decide

/-! ### The verification rows -/

/-- A verification item with the majority response and the majority the stronger mainstream
prediction expects. -/
structure Row where
  quant : Quant
  trial : Trial
  observed : Bool
  predicted : Bool
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let quant ← ex.parse? "quantifier" [("all", Quant.all), ("moreThanOne", .moreThanOne),
    ("exactlyTwo", .exactlyTwo), ("notAll", .notAll), ("notMoreThanOne", .notMoreThanOne)]
  let trial ← ex.parse? "trial" [("none", Trial.none), ("A", .a), ("B", .b)]
  let observed ← ex.nat? "verificationRate"
  let predicted ← ex.nat? "predictedRate"
  pure ⟨quant, trial, decide (50 ≤ observed), decide (50 ≤ predicted)⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

theorem rows_eq : rows = [⟨.all, .none, true, false⟩, ⟨.moreThanOne, .none, true, false⟩,
    ⟨.exactlyTwo, .a, true, false⟩, ⟨.exactlyTwo, .b, false, true⟩, ⟨.notAll, .none, false, false⟩,
    ⟨.notMoreThanOne, .none, false, false⟩] := by
  decide

/-- Each item's situation makes its two construals conflict. -/
theorem rows_construals_conflict :
    ∀ r ∈ rows, (Classical r.quant r.trial ↔ ¬ Local r.quant r.trial) := by
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
  exact ⟨iff_of_true classical_all not_local_all,
    iff_of_true classical_moreThanOne not_local_moreThanOne,
    iff_of_true classical_exactlyTwo_a not_local_exactlyTwo_a,
    iff_of_false not_classical_exactlyTwo_b (not_not.mpr local_exactlyTwo_b),
    iff_of_false not_classical_notAll (not_not.mpr local_notAll),
    iff_of_false not_classical_notMoreThanOne (not_not.mpr local_notMoreThanOne)⟩

/-- Participants' verification responses track the classical construal throughout. -/
theorem rows_observed_classical :
    ∀ r ∈ rows, (r.observed = true ↔ Classical r.quant r.trial) := by
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    true_iff, false_iff, Bool.false_eq_true]
  exact ⟨classical_all, classical_moreThanOne, classical_exactlyTwo_a, not_classical_exactlyTwo_b,
    not_classical_notAll, not_classical_notMoreThanOne⟩

/-- The bracketed predictions are the stronger mainstream construal, derived from the scope
monotonicity of each quantifier; outside downward-entailing scopes they invert the responses. -/
theorem rows_predicted_mainstream :
    ∀ r ∈ rows, (r.predicted = true ↔ Mainstream r.quant r.trial) := by
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    true_iff, false_iff, Bool.false_eq_true, Mainstream]
  refine ⟨?_, ?_, ?_, Or.inl ⟨exactlyTwo_predictsLocalSI, local_exactlyTwo_b⟩, ?_, ?_⟩
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact not_local_all h
    · exact h all_predictsLocalSI
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact not_local_moreThanOne h
    · exact h moreThanOne_predictsLocalSI
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact not_local_exactlyTwo_a h
    · exact h exactlyTwo_predictsLocalSI
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact h (not_not.mp notAll_not_predictsLocalSI)
    · exact not_classical_notAll h
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact h (not_not.mp notMoreThanOne_not_predictsLocalSI)
    · exact not_classical_notMoreThanOne h

end GeurtsPouscoulous2009
