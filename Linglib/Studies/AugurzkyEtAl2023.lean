module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Studies.KrizChemla2015
public import Linglib.Data.Examples.AugurzkyEtAl2023

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

* `Operator`: the quantifiers as van Benthem number trees.
* `Context`, `Context.designation`, `Context.resolve`: the existential and universal questions
  and the designation standard at which each resolves a partially opened set of presents.
* `implicature`, `nonImplicature`: the two verdicts on a display, built on the some- and
  all-substituted readings and the supervaluation of Križ and Chemla; `Strengthens`, the
  quantifiers that are not scope antitone.
* `mixed`, `table2`: the mixed pictures and the derived predictions of both approaches.
* `rows_*`: which rows each approach fits and which it misses.

## Main results

* `nonImplicature_eq`: the non-implicature verdict is classical truth at the resolution the
  context picks.

## References

* [augurzky-etal-2023]
* [kriz-chemla-2015] — the displays and the gap paradigm
* [magri-2014], [bar-lev-2021] — the implicature approach
* [kriz-2016], [kriz-spector-2021] — the non-implicature approach
-/

@[expose] public section

namespace AugurzkyEtAl2023

open Data.Examples Quantifier
open Trivalent (Designation designated)
open KrizChemla2015 (Display resolve reading someReading allReading supervaluation gapValue_of_iff
  gapValue_eq_indet_iff)

/-! ### Quantifiers -/

/-- The quantifiers of the experiments, *every*, *no* and *not every*, and *exactly two*, the test
the paper proposes for the non-implicature approach. -/
inductive Operator where
  | every
  | no
  | notEvery
  | exactlyTwo
  deriving DecidableEq, Fintype

/-- The number tree each quantifier denotes. -/
def Operator.tree : Operator → NumberTree
  | .every => NumberTree.all
  | .no => NumberTree.no
  | .notEvery => NumberTree.notAll
  | .exactlyTwo => NumberTree.cardinal {2}

instance : (op : Operator) → DecidableRel op.tree
  | .every => inferInstanceAs (DecidableRel NumberTree.all)
  | .no => inferInstanceAs (DecidableRel NumberTree.no)
  | .notEvery => inferInstanceAs (DecidableRel NumberTree.notAll)
  | .exactlyTwo => inferInstanceAs (DecidableRel (NumberTree.cardinal {2}))

/-! ### Contexts -/

/-- What the context makes relevant about a boy's presents: whether any were opened, or whether
    all were. -/
inductive Context
  | existential
  | universal
  deriving DecidableEq, Fintype

/-- The resolution of a partially opened set that each question induces: the existential question
    designates what is not false, the universal one only what is true. -/
def Context.designation : Context → Designation
  | .existential => .lp
  | .universal => .k3

/-- Under the existential question a partially opened set of presents counts as opened, under
    the universal one as not opened. -/
def Context.resolve (ctx : Context) (v : Trivalent) : Trivalent :=
  .ofProp (designated ctx.designation v)

theorem resolve_isDefined (ctx : Context) (v : Trivalent) : (ctx.resolve v).isDefined := by
  cases ctx <;> cases v <;> decide

/-- A resolved display looks the same at every standard: the context's. -/
theorem resolve_map_resolve (δ : Designation) (ctx : Context) (d : Display) :
    resolve δ (d.map ctx.resolve) = resolve ctx.designation d := by
  simp only [resolve, List.map_map]
  exact List.map_congr_left fun v _ ↦ by
    simp [Function.comp, Context.resolve, Trivalent.ofProp, Trivalent.designated_ofBool]

/-! ### The two approaches -/

/-- The non-implicature verdict: the sentence's trivalent value, a gap being resolved by the
    question the context makes relevant. -/
def nonImplicature (ctx : Context) (op : Operator) (d : Display) : Trivalent :=
  if supervaluation op.tree d = .indet then supervaluation op.tree (d.map ctx.resolve)
  else supervaluation op.tree d

/-- The context always settles the verdict. -/
theorem nonImplicature_ne_indet (ctx : Context) (op : Operator) (d : Display) :
    nonImplicature ctx op d ≠ .indet := by
  unfold nonImplicature
  split_ifs with h
  · exact KrizChemla2015.supervaluation_ne_indet fun v hv ↦ by
      obtain ⟨v', -, rfl⟩ := List.mem_map.1 hv
      exact resolve_isDefined ctx v'
  · exact h

/-- The non-implicature verdict is classical truth at the resolution the context picks: where the
    sentence has a gap the question resolves it, and elsewhere the two resolutions agree. -/
theorem nonImplicature_eq (ctx : Context) (op : Operator) (d : Display) :
    nonImplicature ctx op d = .ofProp (reading op.tree d ctx.designation) := by
  have hres (δ) : reading op.tree (d.map ctx.resolve) δ ↔ reading op.tree d ctx.designation := by
    rw [reading, reading, resolve_map_resolve]
  unfold nonImplicature supervaluation
  split_ifs with h
  · rw [gapValue_of_iff ((hres _).trans (hres _).symm)]
    exact congrArg Trivalent.ofBool (decide_eq_decide.2 (hres _))
  · have hsa : someReading op.tree d ↔ allReading op.tree d := not_not.1 fun h' ↦
      h (gapValue_eq_indet_iff.2 h')
    rw [gapValue_of_iff hsa]
    cases ctx
    · rfl
    · exact congrArg Trivalent.ofBool (decide_eq_decide.2 hsa)

/-- Implicatures arise in the scope of an operator unless it is downward entailing, as *no* and
    *not every* are. -/
def Strengthens (op : Operator) : Prop := ¬ op.tree.ScopeAntitone

instance : DecidablePred Strengthens := fun op ↦
  decidable_of_iff (op = .every ∨ op = .exactlyTwo) <| by
    cases op
    · exact iff_of_true (.inl rfl) fun h ↦ absurd (h 0 0 rfl) (Nat.succ_ne_zero 0)
    · exact iff_of_false (by decide) (not_not.2 NumberTree.scopeAntitone_no)
    · exact iff_of_false (by decide) (not_not.2 NumberTree.scopeAntitone_notAll)
    · exact iff_of_true (.inr rfl) fun h ↦ absurd (h 1 1 rfl) (by decide)

/-- The implicature verdict: the existential literal meaning, strengthened to the universal
    reading where implicatures arise, unless the context prunes the alternatives. -/
def implicature (ctx : Context) (op : Operator) (d : Display) : Prop :=
  someReading op.tree d ∧ (ctx = .universal → Strengthens op → allReading op.tree d)

instance (ctx : Context) (op : Operator) (d : Display) :
    Decidable (implicature ctx op d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### The experiments -/

-- UNVERIFIED: the paper's text describes Experiment 2's mixed picture as two boys with all and
-- two with none of their presents open, which makes *not every* bivalently true; its Table 2 and
-- the context effect it reports for both quantifiers need the some-but-not-all picture below.
/-- The mixed pictures: two of four boys with all their presents open and two with some but not
    all, for *every* and *not every*; two with none and two with some for *no*; and the paper's
    proposed test for *exactly two*, two boys with some and the others with none. -/
def mixed : Operator → Display
  | .every | .notEvery => [.true, .true, .indet, .indet]
  | .no => [.false, .false, .indet, .indet]
  | .exactlyTwo => [.indet, .indet, .false, .false]

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
def operator? (r : LinguisticExample) : Option Operator :=
  r.parse? "operator" [("every", .every), ("no", .no), ("notEvery", .notEvery)]

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
