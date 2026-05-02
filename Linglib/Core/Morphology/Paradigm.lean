import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Linglib.Core.Morphology.MorphRule
import Mathlib.Data.Rat.Defs

/-!
# Morphological Paradigm Substrate
@cite{ackerman-malouf-2013} @cite{rathi-hahn-futrell-2026}

Cross-paper substrate for paradigm-cell-level analyses: inflection classes,
paradigm systems, cell distributions, and entropy-based measures over them.

`Core.Morphology.ParadigmCell` (in `MorphRule.lean`) is the type for **one
cell** of a paradigm with its features and form; `ParadigmSystem` here is the
**whole table** with frequency weights, organized by inflection class.

## Form parameterization

`InflectionClass n Form` and `ParadigmSystem n Form` are parameterized over
the surface-form type. Most consumers use `Form := String` (the natural
representation for actual morphological forms in @cite{ackerman-malouf-2013}'s
A&M language sample). The Rathi 2026 toy paradigms use a small `[Fintype]`
form alphabet so that PMF-based entropy operators (`PMFEntropy.lean`) apply
to cell distributions; that integration lives in a sibling
`PMFCellDistribution.lean` file added in a later phase of the unification
refactor.

## Public API

- `InflectionClass n Form` — total function `Fin n → Form` from cell index to form
- `ParadigmSystem n Form` — list of inflection classes with frequency weights
- `cellDistribution`, `jointCellDistribution` — empirical distributions
- `cellEntropy`, `conditionalCellEntropy` — Shannon entropies via `Core.InformationTheory`
- `isImplicative`, `isTransparent` — structural predicates on paradigm shape
- `fromStems` — derive a `ParadigmSystem n String` from a list of `Stem σ`
- `eComplexity` — count of inflection classes (Ackerman-Malouf E-complexity)

`iComplexity` (the paper-specific average conditional entropy) and `LCECHolds`
(the LCEC threshold predicate) live in `AckermanMalouf2013.lean` because they
are particular aggregations the paper defines, not substrate primitives.
-/

namespace Core.Morphology

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
   fun a => (((dist.find? (·.1 == a)).map Prod.snd).getD 0 : ℚ))

/-- An inflection class: function from cell index to surface realization
    of type `Form`. -/
structure InflectionClass (numCells : Nat) (Form : Type*) where
  realize : Fin numCells → Form

instance {n : Nat} {Form : Type} [BEq Form] :
    BEq (InflectionClass n Form) where
  beq a b := (List.finRange n).all λ i => a.realize i == b.realize i

/-- A paradigm system: inflection classes paired with frequency weights. -/
structure ParadigmSystem (numCells : Nat) (Form : Type*) where
  entries : List (InflectionClass numCells Form × ℚ)

/-- Group a tagged list by key, summing associated ℚ values. -/
def groupBySum {α : Type} [BEq α] (tagged : List (α × ℚ)) : List (α × ℚ) :=
  tagged.foldl (λ acc (key, f) =>
    match acc.find? (λ (k, _) => k == key) with
    | some _ => acc.map (λ (k, p) => if k == key then (k, p + f) else (k, p))
    | none => acc ++ [(key, f)]
  ) []

/-- Empirical distribution of forms at cell `c`: pairs each surface form with
    the total frequency of inflection classes realizing it at `c`. -/
def ParadigmSystem.cellDistribution {n : Nat} {Form : Type} [BEq Form]
    (ps : ParadigmSystem n Form) (c : Fin n) :
    List (Form × ℚ) :=
  groupBySum (ps.entries.map λ (ic, f) => (ic.realize c, f))

/-- Joint empirical distribution of forms at cell pair `(ci, cj)`. -/
def ParadigmSystem.jointCellDistribution {n : Nat} {Form : Type} [BEq Form]
    (ps : ParadigmSystem n Form) (ci cj : Fin n) :
    List ((Form × Form) × ℚ) :=
  groupBySum (ps.entries.map λ (ic, f) => ((ic.realize ci, ic.realize cj), f))

/-- E-complexity (@cite{ackerman-malouf-2013}): the number of inflection
    classes in the paradigm system. -/
def ParadigmSystem.eComplexity {n : Nat} {Form : Type*}
    (ps : ParadigmSystem n Form) : Nat :=
  ps.entries.length

/-- Shannon entropy of the empirical distribution at cell `c` (in nats). -/
noncomputable def ParadigmSystem.cellEntropy {n : Nat} {Form : Type} [BEq Form]
    [DecidableEq Form] (ps : ParadigmSystem n Form) (c : Fin n) : ℝ :=
  let (support, prob) := distOfList (ps.cellDistribution c)
  entropy support prob

/-- Conditional entropy `H(C_i | C_j)` of cell `ci` given cell `cj` (in nats).
    The integrand of @cite{ackerman-malouf-2013}'s i-complexity. -/
noncomputable def ParadigmSystem.conditionalCellEntropy {n : Nat} {Form : Type}
    [BEq Form] [DecidableEq Form]
    (ps : ParadigmSystem n Form) (ci cj : Fin n) : ℝ :=
  let (sJoint, joint) := distOfList (ps.jointCellDistribution ci cj)
  let (sMargX, margX) := distOfList (ps.cellDistribution cj)
  conditionalEntropy sJoint joint sMargX margX

/-- A cell pair `(ci, cj)` is **implicative** iff knowing the form at `cj`
    perfectly determines the form at `ci` (zero conditional entropy). -/
def ParadigmSystem.isImplicative {n : Nat} {Form : Type} [BEq Form] [DecidableEq Form]
    (ps : ParadigmSystem n Form) (ci cj : Fin n) : Prop :=
  ps.conditionalCellEntropy ci cj = 0

/-- A paradigm is **transparent** iff every off-diagonal cell pair is
    implicative — every cell perfectly predicts every other. -/
def ParadigmSystem.isTransparent {n : Nat} {Form : Type} [BEq Form] [DecidableEq Form]
    (ps : ParadigmSystem n Form) : Prop :=
  ∀ (ci cj : Fin n), ci ≠ cj → ps.isImplicative ci cj

/-- Extract a `ParadigmSystem n String` from a list of `Stem`s. The
    `cellExtractor` function maps each stem's generated forms (with their
    features and base meaning) to a per-cell surface realization.
    Specialized to `Form := String` since `Stem`'s `allForms` returns
    `String`-typed surface forms. -/
def ParadigmSystem.fromStems {σ : Type} (stems : List (Core.Morphology.Stem σ))
    (baseMeaning : σ) (numCells : Nat)
    (cellExtractor : List (String × Features × σ) → Fin numCells → String) :
    ParadigmSystem numCells String :=
  let allParadigms := stems.map λ s =>
    let forms := s.allForms baseMeaning
    { realize := cellExtractor forms : InflectionClass numCells String }
  let total := stems.length
  let unique := groupBySum (allParadigms.map λ ic => (ic, (1 : ℚ)))
  { entries := unique.map λ (ic, count) => (ic, count / total) }

end Core.Morphology
