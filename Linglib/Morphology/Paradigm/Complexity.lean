import Linglib.Morphology.Paradigm.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Paradigm complexity: entropy and implicative structure over cells

Two views of the Paradigm Cell Filling Problem over a `ParadigmSystem`.
The **quantitative** layer measures cell distributions: Shannon entropy
of a cell, conditional entropy between cells (the integrand of
[ackerman-malouf-2013]'s i-complexity), and the derived
implicative-structure predicates. The **qualitative** layer is the
zero-entropy (categorical) case: a set of cells `Predicts` another when
the forms filling it determine the form filling the target across every
inflection class — the implicative relation [bonami-beniamine-2016]
quantify with conditional entropy, here as a plain relation over the
system's rows. Entropy quantification stays prose-level per repo
discipline; `Predicts` is its zero-entropy extreme.

## Main declarations

* `ParadigmSystem.cellEntropy`, `ParadigmSystem.conditionalCellEntropy`
* `ParadigmSystem.isImplicative`, `ParadigmSystem.isTransparent`
* `ParadigmSystem.Predicts`, `ParadigmSystem.IsPrincipalPartSet` — the
  categorical implicative relation and principal-part sets

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

/-! ### Qualitative implicative structure

The categorical (zero-entropy) face of the Paradigm Cell Filling
Problem [bonami-beniamine-2016]: which sets of known cells determine an
unknown cell across the inflection classes. -/

/-- A set of cells `S` **predicts** cell `j` when the forms filling `S`
determine the form filling `j` across the system: any two inflection
classes agreeing on every cell of `S` also agree at `j`. The
zero-conditional-entropy case of the implicative relation
[bonami-beniamine-2016] measure. -/
def ParadigmSystem.Predicts {n : ℕ} {Form : Type*}
    (ps : ParadigmSystem n Form) (S : Finset (Fin n)) (j : Fin n) : Prop :=
  ∀ p ∈ ps.entries, ∀ q ∈ ps.entries,
    (∀ c ∈ S, p.1 c = q.1 c) → p.1 j = q.1 j

/-- A set of cells is a **principal-part set** when it predicts every cell
of the system: knowing those forms determines the whole paradigm. -/
def ParadigmSystem.IsPrincipalPartSet {n : ℕ} {Form : Type*}
    (ps : ParadigmSystem n Form) (S : Finset (Fin n)) : Prop :=
  ∀ j, ps.Predicts S j

/-- Prediction is **monotone** in the known cells: enlarging the predictor
set never destroys a prediction. -/
theorem ParadigmSystem.Predicts.mono {n : ℕ} {Form : Type*}
    {ps : ParadigmSystem n Form} {S T : Finset (Fin n)} {j : Fin n}
    (hST : S ⊆ T) (h : ps.Predicts S j) : ps.Predicts T j :=
  fun p hp q hq hag => h p hp q hq fun c hc => hag c (hST hc)

/-- A worked case: a two-class system whose first cell is diagnostic. The
classes differ at cell `0`, so it is a principal-part set — its form
determines cell `1`. -/
private def demoSystem : ParadigmSystem 2 String :=
  { entries := [(![("a"), ("x")], 1 / 2), (![("b"), ("y")], 1 / 2)] }

private theorem demoSystem_principalPart :
    demoSystem.IsPrincipalPartSet {0} := by
  intro j; fin_cases j <;> (unfold ParadigmSystem.Predicts; decide)

end Morphology
