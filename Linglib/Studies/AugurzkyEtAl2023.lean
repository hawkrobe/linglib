import Mathlib.Tactic.DeriveFintype
import Linglib.Studies.KrizChemla2015
import Linglib.Data.Examples.AugurzkyEtAl2023

/-!
# Augurzky et al. 2023: plural definites in context

Plural definites are homogeneous — *every boy opened his presents* is understood as *all* of
them, its negation as *none* — and non-maximal: where all that matters is whether any present
was opened, the sentence passes though a few presents stayed closed. The implicature approach
gives the definite an existential meaning, strengthened to the universal by an implicature in
positive environments only, so that pruning alternatives yields non-maximality there and
nowhere else. The non-implicature approach gives the sentence a truth-value gap in mixed
scenarios and lets what the context makes relevant group the gap with truth or with falsity,
symmetrically for positive and negative sentences. Two picture-verification experiments put the
plural definite under *every*, *no* and *not every* while manipulating whether the family rule
made it relevant that any or that all presents be opened. Under *every* the mixed picture is
accepted in the existential context and rejected in the universal one, as both approaches
predict; under *no* it is rejected in both, with only a small context effect, as the
implicature approach predicts; under *not every* it is accepted in the universal context and
rejected in the existential one, as only the non-implicature approach predicts. Each approach
is therefore challenged by one negative quantifier.

## Main definitions

* `Context`, `Context.resolve`: the existential and universal questions and how each resolves a
  partially opened set of presents.
* `implicature`, `nonImplicature`: the two verdicts on a display, built on the some- and
  all-substituted readings and the supervaluation of Križ and Chemla.
* `mixed`, `table2`: the mixed pictures and the derived predictions of both approaches.
* `rows_*`: which rows each approach fits and which it misses.

## References

* [augurzky-etal-2023]
* [kriz-chemla-2015] — the displays and the gap paradigm
* [magri-2014], [bar-lev-2021] — the implicature approach
* [kriz-2016], [kriz-spector-2021] — the non-implicature approach
-/

namespace AugurzkyEtAl2023

open Data.Examples
open Generalizations.HomogeneityProjection (EmbeddingOperator parseOperator)
open KrizChemla2015 (Cell Display someReading allReading gapValue supervaluation)

/-! ### Contexts -/

/-- What the context makes relevant about a boy's presents: whether any were opened, or whether
    all were. -/
inductive Context
  | existential
  | universal
  deriving DecidableEq, Fintype

/-- Under the existential question a partially opened set of presents counts as opened, under
    the universal one as not opened. -/
def Context.resolve : Context → Cell → Cell
  | .existential, .mixed => .full
  | .universal, .mixed => .empty
  | _, c => c

theorem resolve_homogeneous (ctx : Context) (c : Cell) : (ctx.resolve c).homogeneous := by
  cases ctx <;> cases c <;> decide

/-! ### The two approaches -/

/-- Two readings that agree yield a bivalent verdict. -/
theorem gapValue_ne_indet {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    gapValue p q ≠ .indet := by
  unfold gapValue
  by_cases hp : p
  · simp [hp, h.1 hp]
  · simp [hp, mt h.2 hp]

/-- On a display without partially opened presents the some- and all-substituted readings
    coincide, so the supervaluation is bivalent. -/
theorem supervaluation_ne_indet (op : EmbeddingOperator) (d : Display)
    (h : ∀ c ∈ d, c.homogeneous) : supervaluation op d ≠ .indet := by
  refine gapValue_ne_indet ?_
  have hc : ∀ c ∈ d, (c ≠ .empty ↔ c = .full) := λ c hc => by
    have := h c hc; cases c <;> simp_all [Cell.homogeneous]
  cases op
  · exact forall₂_congr hc
  · exact forall₂_congr λ c hc' => by have := h c hc'; cases c <;> simp_all [Cell.homogeneous]
  · show KrizChemla2015.occupied d = 2 ↔ KrizChemla2015.filled d = 2
    unfold KrizChemla2015.occupied KrizChemla2015.filled
    have hcount : d.countP (· != Cell.empty) = d.countP (· == Cell.full) :=
      List.countP_congr λ c hc' => by have := h c hc'; cases c <;> simp_all [Cell.homogeneous]
    rw [List.count_eq_countP, hcount]
  · exact not_congr (forall₂_congr hc)

/-- The non-implicature verdict: the sentence's trivalent value, a gap being resolved by the
    question the context makes relevant. -/
def nonImplicature (ctx : Context) (op : EmbeddingOperator) (d : Display) : Trivalent :=
  if supervaluation op d = .indet then supervaluation op (d.map ctx.resolve)
  else supervaluation op d

/-- The context always settles the verdict. -/
theorem nonImplicature_ne_indet (ctx : Context) (op : EmbeddingOperator) (d : Display) :
    nonImplicature ctx op d ≠ .indet := by
  unfold nonImplicature
  split_ifs with h
  · exact supervaluation_ne_indet _ _ λ c hc => by
      obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc
      exact resolve_homogeneous ctx c'
  · exact h

/-- Implicatures arise in the scope of an operator unless it is downward entailing, as *no* and
    *not every* are. -/
def Strengthens : EmbeddingOperator → Prop
  | .no | .notEvery => False
  | _ => True

instance : DecidablePred Strengthens := λ op => by
  cases op <;> simp only [Strengthens] <;> infer_instance

/-- The implicature verdict: the existential literal meaning, strengthened to the universal
    reading where implicatures arise, unless the context prunes the alternatives. -/
def implicature (ctx : Context) (op : EmbeddingOperator) (d : Display) : Prop :=
  someReading op d ∧ (ctx = .universal → Strengthens op → allReading op d)

instance (ctx : Context) (op : EmbeddingOperator) (d : Display) :
    Decidable (implicature ctx op d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### The experiments -/

-- UNVERIFIED: the paper's text describes Experiment 2's mixed picture as two boys with all and
-- two with none of their presents open, which makes *not every* bivalently true; its Table 2 and
-- the context effect it reports for both quantifiers need the some-but-not-all picture below.
/-- The mixed pictures: two of four boys with all their presents open and two with some but not
    all, for *every* and *not every*; two with none and two with some for *no*; and the paper's
    proposed test for *exactly two*, two boys with some and the others with none. -/
def mixed : EmbeddingOperator → Display
  | .every | .notEvery => [.full, .full, .mixed, .mixed]
  | .no => [.empty, .empty, .mixed, .mixed]
  | .exactlyTwo => [.mixed, .mixed, .empty, .empty]

/-- The derived predictions for the mixed pictures: both approaches accept *every* exactly in
    the existential context; the implicature approach rejects *no* and *not every* in both
    contexts, the non-implicature approach accepts both exactly in the universal context. -/
theorem table2 : ∀ ctx : Context,
    (implicature ctx .every (mixed .every) ↔ ctx = .existential) ∧
      ¬ implicature ctx .no (mixed .no) ∧ ¬ implicature ctx .notEvery (mixed .notEvery) ∧
      (nonImplicature ctx .every (mixed .every) = .true ↔ ctx = .existential) ∧
      (nonImplicature ctx .no (mixed .no) = .true ↔ ctx = .universal) ∧
      (nonImplicature ctx .notEvery (mixed .notEvery) = .true ↔ ctx = .universal) := by
  decide

/-- The operator of a row's sentence. -/
def operator? (r : LinguisticExample) : Option EmbeddingOperator :=
  (r.feature? "operator").bind parseOperator

/-- The question a row's context makes relevant. -/
def context? (r : LinguisticExample) : Option Context :=
  match r.feature? "qud" with
  | some "existential" => some .existential
  | some "universal" => some .universal
  | _ => none

/-- Whether a row's mixed picture was rated high. -/
def High (r : LinguisticExample) : Prop := r.feature? "rating" = some "high"

instance (r : LinguisticExample) : Decidable (High r) := inferInstanceAs (Decidable (_ = _))

/-- The implicature approach fits every row under *every* and *no*. -/
theorem rows_implicature :
    ∀ r ∈ Examples.all, ∀ op ∈ operator? r, ∀ ctx ∈ context? r, op ≠ .notEvery →
      (High r ↔ implicature ctx op (mixed op)) := by
  decide

/-- It misses *not every*, which the universal context rescues as it does *every*. -/
theorem rows_implicature_notEvery :
    ∀ r ∈ Examples.all, ∀ op ∈ operator? r, ∀ ctx ∈ context? r, op = .notEvery →
      (High r ↔ ctx = .universal) ∧ ¬ implicature ctx op (mixed op) := by
  decide

/-- The non-implicature approach fits every row under *every* and *not every*. -/
theorem rows_nonImplicature :
    ∀ r ∈ Examples.all, ∀ op ∈ operator? r, ∀ ctx ∈ context? r, op ≠ .no →
      (High r ↔ nonImplicature ctx op (mixed op) = .true) := by
  decide

/-- It misses *no*, which the universal context should rescue but does not. -/
theorem rows_nonImplicature_no :
    ∀ r ∈ Examples.all, ∀ op ∈ operator? r, ∀ ctx ∈ context? r, op = .no →
      ¬ High r ∧ (nonImplicature ctx op (mixed op) = .true ↔ ctx = .universal) := by
  decide

end AugurzkyEtAl2023
