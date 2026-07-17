import Linglib.Morphology.Paradigm.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Paradigm complexity: entropy over cell distributions
[ackerman-malouf-2013] [rathi-hahn-futrell-2026]

Entropy-based measures over `ParadigmSystem` cell distributions:
Shannon entropy of a cell, conditional entropy between cells (the
integrand of [ackerman-malouf-2013]'s i-complexity), and the derived
implicative-structure predicates.

## Main declarations

* `ParadigmSystem.cellEntropy`, `ParadigmSystem.conditionalCellEntropy`
* `ParadigmSystem.isImplicative`, `ParadigmSystem.isTransparent`

`iComplexity` (the paper-specific average conditional entropy) and
`LCECHolds` (the LCEC threshold predicate) live in
`Studies/AckermanMalouf2013.lean` because they are particular
aggregations the paper defines, not substrate primitives.
-/

namespace Morphology

/-- **Private (ι→ℝ) Shannon entropy** for paradigm-cell complexity computations.
    Inlined from the deleted `Core.InformationTheory.entropy` (the canonical PMF
    form is `PMF.entropy`; this Finset-restricted (ι→ℝ) form is natural here
    because cell distributions are list-derived ad-hoc empirical frequencies). -/
private noncomputable def entropy {α : Type*} (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ a ∈ s, Real.negMulLog (p a)

/-- **Private conditional entropy** `H(Y|X) = H(X,Y) − H(X)`. -/
private noncomputable def conditionalEntropy {α β : Type*}
    (sJoint : Finset (α × β)) (joint : α × β → ℝ)
    (sX : Finset α) (marginalX : α → ℝ) : ℝ :=
  entropy sJoint joint - entropy sX marginalX

/-- **Private list-of-pairs → (Finset, function) adapter** (was
    `Core.InformationTheory.distOfList`). -/
private noncomputable def distOfList {α : Type*} [DecidableEq α]
    (dist : List (α × ℚ)) : Finset α × (α → ℝ) :=
  ((dist.map Prod.fst).toFinset,
   fun a => (((dist.find? (λ x => x.1 = a)).map Prod.snd).getD 0 : ℚ))

/-- Shannon entropy of the empirical distribution at cell `c` (in nats). -/
noncomputable def ParadigmSystem.cellEntropy {n : ℕ} {Form : Type*}
    [DecidableEq Form] (ps : ParadigmSystem n Form) (c : Fin n) : ℝ :=
  let (support, prob) := distOfList (ps.cellDistribution c)
  entropy support prob

/-- Conditional entropy `H(C_i | C_j)` of cell `ci` given cell `cj` (in nats).
    The integrand of [ackerman-malouf-2013]'s i-complexity. -/
noncomputable def ParadigmSystem.conditionalCellEntropy {n : ℕ} {Form : Type*}
    [DecidableEq Form]
    (ps : ParadigmSystem n Form) (ci cj : Fin n) : ℝ :=
  let (sJoint, joint) := distOfList (ps.jointCellDistribution ci cj)
  let (sMargX, margX) := distOfList (ps.cellDistribution cj)
  conditionalEntropy sJoint joint sMargX margX

/-- A cell pair `(ci, cj)` is **implicative** iff knowing the form at `cj`
    perfectly determines the form at `ci` (zero conditional entropy). -/
def ParadigmSystem.isImplicative {n : ℕ} {Form : Type*} [DecidableEq Form]
    (ps : ParadigmSystem n Form) (ci cj : Fin n) : Prop :=
  ps.conditionalCellEntropy ci cj = 0

/-- A paradigm is **transparent** iff every off-diagonal cell pair is
    implicative — every cell perfectly predicts every other. -/
def ParadigmSystem.isTransparent {n : ℕ} {Form : Type*} [DecidableEq Form]
    (ps : ParadigmSystem n Form) : Prop :=
  ∀ (ci cj : Fin n), ci ≠ cj → ps.isImplicative ci cj

end Morphology
