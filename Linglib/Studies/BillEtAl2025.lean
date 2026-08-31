import Linglib.Semantics.Intensional.Conjunction
import Linglib.Semantics.Plurality.Distributivity
import Linglib.Syntax.Coordination
import Linglib.Studies.Haspelmath2007
import Linglib.Studies.MitrovicSauerland2016

/-!
# Bill, Gonzalez, Driemel, Makharoblidze and Pintér 2025: is DP conjunction always complex?

This file formalizes the argument of Bill and colleagues' comprehension study of conjunctive
expressions in Georgian and Hungarian. Both languages express DP conjunction with a *j*
particle alone, with a *mu* particle on each conjunct, or with both. Under Mitrović and
Sauerland's decomposition every strategy realizes the same three-piece structure — *j* as
intersection and two *mu*s as subset operators over singleton-shifted conjuncts — and, with
the Transparency Principle that children comprehend one-to-one form–meaning mappings more
easily, the fully overt *j-mu* expressions are predicted to be the easiest. Georgian
children replayed *j-mu* sentences more often than *j* or *mu* sentences, with no difference
between the latter two, and Hungarian children showed no difference at all; so the
prediction fails, as does the ordering of the accounts on which *j* is structurally simplest
and *mu* and *j-mu* share one structure. The paper concludes that an adequate account must
make *j-mu* more complex than *j* and *mu*, make *j* and *mu* equally complex, and make
Hungarian *mu* less complex than Georgian *mu*.

## Main definitions

* `covertPieces`: the pieces of the decomposition a strategy leaves unpronounced, the
  Transparency Principle's measure of difficulty.
* `structuralPieces`: the pieces of the rival structures, one for *j* and three for *mu*
  and *j-mu*.
* `georgianHarder`: the significant comprehension contrasts among Georgian children.
* `Desiderata`: the paper's conditions on a complexity measure.

## Main results

* `transparency_prediction`: the decomposition with the Transparency Principle predicts
  *j-mu* easiest.
* `georgian_contradicts_transparency`, `georgian_contradicts_structural`: the observed
  contrasts reverse the first prediction and split the strategies the rival equates.
* `covertPieces_not_desiderata`, `structuralPieces_not_desiderata`: neither measure meets
  the desiderata.
* `ms_decomposition_eq_coord`, `mu_is_distributive_check`: the decomposition computes
  ordinary distributive conjunction.

## References

* [bill-etal-2025]
* [mitrovic-sauerland-2014], [mitrovic-sauerland-2016]: the decomposition.
* [van-hout-1998]: the Transparency Principle.
* [szabolcsi-2015], [haslinger-etal-2019]: the rival structures.
* [clark-2017]: bound versus free morphemes in acquisition.
-/

namespace BillEtAl2025

open Syntax.Coordination Haspelmath2007 MitrovicSauerland2016

/-- Both test languages attest all three strategies, the precondition of the test ((1),
(2)). -/
theorem both_have_all_three :
    hasAllThreeStrategies georgian ∧ hasAllThreeStrategies hungarian := by
  decide

/-! ### The prediction -/

/-- The pieces of the three-piece decomposition a strategy leaves unpronounced: the
Transparency Principle's measure of comprehension difficulty (3). -/
def covertPieces (s : ConjunctionStrategy) : ℕ :=
  ConjunctionStrategy.semanticPieceCount - s.overtMorphemeCount

/-- The decomposition with the Transparency Principle predicts the fully overt *j-mu*
expressions easiest (4). -/
theorem transparency_prediction :
    covertPieces .jMu < covertPieces .jOnly ∧ covertPieces .jMu < covertPieces .muOnly := by
  decide

/-- The pieces of the rival structures: a lone *j* for *j* expressions, a *j* with two
*mu*s for *mu* and *j-mu* expressions (Figure 1). -/
def structuralPieces : ConjunctionStrategy → ℕ
  | .jOnly => 1
  | .muOnly => 3
  | .jMu => 3

/-! ### The finding -/

/-- The significant contrasts in Georgian children's replay counts (Table 3): *j-mu*
sentences were harder than *j* and than *mu* sentences, and *j* and *mu* did not differ. -/
def georgianHarder : ConjunctionStrategy → ConjunctionStrategy → Prop
  | .jMu, .jOnly => True
  | .jMu, .muOnly => True
  | _, _ => False

/-- The harder expressions were the more transparent ones: the prediction is reversed. -/
theorem georgian_contradicts_transparency (s t : ConjunctionStrategy) (h : georgianHarder s t) :
    covertPieces s < covertPieces t := by
  cases s <;> cases t <;> simp [georgianHarder] at h <;> decide

/-- The rival structures equate *mu* and *j-mu*, which the Georgian children split. -/
theorem georgian_contradicts_structural :
    ∃ s t, georgianHarder s t ∧ structuralPieces s = structuralPieces t :=
  ⟨.jMu, .muOnly, trivial, rfl⟩

/-! ### The desiderata -/

/-- The paper's conditions on a complexity measure: *j-mu* more complex than *j* and than
*mu*, and *j* and *mu* equally complex. -/
def Desiderata (c : ConjunctionStrategy → ℕ) : Prop :=
  c .jOnly < c .jMu ∧ c .muOnly < c .jMu ∧ c .jOnly = c .muOnly

instance (c : ConjunctionStrategy → ℕ) : Decidable (Desiderata c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem covertPieces_not_desiderata : ¬ Desiderata covertPieces := by decide

theorem structuralPieces_not_desiderata : ¬ Desiderata structuralPieces := by decide

/-- The third desideratum's morphological route: Georgian *mu* is a bound clitic where
Hungarian *mu* is free, the difference the paper suggests may make Hungarian *mu* the less
complex. -/
theorem mu_kind_differs :
    georgian.muKind = some (.bound .after .clitic) ∧ hungarian.muKind = some .free := by
  decide

/-! ### The decomposition -/

open Intensional.Conjunction in
open Quantification (individual) in
/-- The decomposition — singleton shift, subset, intersection — is the substrate's
`coordEntities`, so *DP₁ and DP₂ VP* comes out as `VP(DP₁) ∧ VP(DP₂)` (Figure 2). -/
theorem ms_decomposition_eq_coord {E W : Type} (e1 e2 : E) (p : E → Prop) :
    (individual (α := E) e1 p ∧ individual (α := E) e2 p) =
      coordEntities (E := E) (W := W) e1 e2 p :=
  rfl

open Intensional.Conjunction in
open Quantification (individual) in
open Plurality in
open Plurality.Distributivity in
/-- The decomposition is distributive predication over the pair of conjuncts. -/
theorem mu_is_distributive_check {E W : Type} [DecidableEq E]
    (e1 e2 : E) (P : E → Unit → Prop) [∀ a u, Decidable (P a u)] :
    coordEntities (E := E) (W := W) e1 e2 (fun a => P a ()) ↔
    distMaximal P {e1, e2} () := by
  simp [coordEntities_both_satisfy, distMaximal_pair]

end BillEtAl2025
