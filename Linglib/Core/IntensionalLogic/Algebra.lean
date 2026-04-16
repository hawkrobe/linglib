import Linglib.Core.IntensionalLogic.Quantification
import Linglib.Core.IntensionalLogic.Conjunction
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Heyting.Basic

/-!
# Algebraic Structure of IL Denotation Domains

@cite{dowty-wall-peters-1981} @cite{gallin-1975} @cite{partee-rooth-1983}

The IL operators in `Frame.lean`, `Quantification.lean`, and `Conjunction.lean`
are instances of general algebraic operations from mathlib's order theory.

The central observation: **Montague's type-driven semantics is a hierarchy of
pointwise Boolean algebras.** Every conjoinable type `τ` (one that "ends in `t`")
induces a `CompleteLattice` on `F.Denot τ`:

- At type `t`: the Boolean algebra of propositions (`Prop`)
- At type `⟨a, t⟩`: the pointwise Boolean algebra of predicates
- At type `⟨s, t⟩`: the Boolean algebra of propositions (= sets of indices)
- At type `⟨a, ⟨b, t⟩⟩`: the doubly-pointwise Boolean algebra

The IL operators are lattice operations in this hierarchy:

| IL operator | Lattice operation | mathlib name |
|-------------|-------------------|--------------|
| `neg`       | complement        | `compl` (ᶜ) |
| `conj`      | meet              | `inf` (⊓)   |
| `disj`      | join              | `sup` (⊔)   |
| `impl`      | Heyting implication | `himp` (⇨) |
| `box`       | indexed infimum   | `iInf` (⨅)  |
| `diamond`   | indexed supremum  | `iSup` (⨆)  |
| `forallEntity` | indexed infimum | `iInf` (⨅) |
| `existsEntity` | indexed supremum | `iSup` (⨆) |
| `genConj`   | pointwise meet    | `Pi.inf`     |
| `genDisj`   | pointwise join    | `Pi.sup`     |

@cite{partee-rooth-1983}'s generalized conjunction is the pointwise
meet in the lattice of type `τ` — a fact that explains *why* conjunction
is defined recursively over types and *why* it only works for
conjoinable types (those admitting a lattice structure).
-/

namespace Core.IntensionalLogic.Algebra

open Core.IntensionalLogic

variable {F : Frame}

-- ════════════════════════════════════════════════════════════════
-- § Propositional Boolean Algebra
-- ════════════════════════════════════════════════════════════════

/-! `F.Denot .t = Prop` is a `CompleteBooleanAlgebra` (via mathlib's
`Prop.instCompleteLattice` and `Prop.instHeytingAlgebra`). The IL
sentential operators are its algebraic operations. -/

theorem neg_eq_compl (p : F.Denot .t) : neg p = (show Prop from p)ᶜ := rfl
theorem conj_eq_inf (p q : F.Denot .t) : conj p q = (show Prop from p) ⊓ q := rfl
theorem disj_eq_sup (p q : F.Denot .t) : disj p q = (show Prop from p) ⊔ q := rfl
theorem impl_eq_himp (p q : F.Denot .t) : impl p q = ((show Prop from p) ⇨ q) := rfl

-- ════════════════════════════════════════════════════════════════
-- § Modal Algebra: box/diamond as iInf/iSup
-- ════════════════════════════════════════════════════════════════

/-! `box` and `diamond` are the indexed infimum and supremum over
the index set — the lattice-theoretic formulation of S5 necessity
and possibility. -/

theorem box_eq_iInf (p : F.Denot .prop) :
    box (F := F) p = ⨅ i, (show Prop from p i) :=
  iInf_Prop_eq.symm

theorem diamond_eq_iSup (p : F.Denot .prop) :
    diamond (F := F) p = ⨆ i, (show Prop from p i) :=
  iSup_Prop_eq.symm

/-- `box` is monotone: if `p i → q i` at every index, then `□p → □q`. -/
theorem box_mono {p q : F.Denot .prop}
    (h : ∀ i, p i → q i) : box (F := F) p → box q :=
  fun hp i => h i (hp i)

/-- `diamond` is monotone. -/
theorem diamond_mono {p q : F.Denot .prop}
    (h : ∀ i, p i → q i) : diamond (F := F) p → diamond q :=
  fun ⟨i, hi⟩ => ⟨i, h i hi⟩

-- ════════════════════════════════════════════════════════════════
-- § Quantifier Algebra: forallEntity/existsEntity as iInf/iSup
-- ════════════════════════════════════════════════════════════════

theorem forallEntity_eq_iInf (body : F.Entity → F.Denot .t) :
    forallEntity body = ⨅ x, (show Prop from body x) :=
  iInf_Prop_eq.symm

theorem existsEntity_eq_iSup (body : F.Entity → F.Denot .t) :
    existsEntity body = ⨆ x, (show Prop from body x) :=
  iSup_Prop_eq.symm

-- ════════════════════════════════════════════════════════════════
-- § Generalized Conjunction = Pointwise Meet
-- ════════════════════════════════════════════════════════════════

/-! @cite{partee-rooth-1983}'s generalized conjunction is the pointwise
meet in the lattice of the codomain type. This explains why `genConj`
is defined recursively: it follows the recursive lattice construction
on `Pi` types.

The proofs are `rfl` because `genConj` unfolds to exactly the same
function as the pointwise `inf` from `Pi.instLattice`. -/

open Conjunction

/-- At type `t`: generalized conjunction is propositional `∧` = `⊓`. -/
theorem genConj_eq_inf_t (p q : F.Denot .t) :
    genConj .t F p q = (show Prop from p) ⊓ q := rfl

/-- At type `t`: generalized disjunction is propositional `∨` = `⊔`. -/
theorem genDisj_eq_sup_t (p q : F.Denot .t) :
    genDisj .t F p q = (show Prop from p) ⊔ q := rfl

/-! At function and intension types, `genConj`/`genDisj` distribute
pointwise (Conjunction.lean, Facts 6a–6c). The recursive structure
mirrors the pointwise lattice construction `Pi.instLattice`:
at each layer, `genConj` applies `⊓` on the codomain / base type.
The base case above closes the induction. -/

-- ════════════════════════════════════════════════════════════════
-- § De Morgan Laws (from lattice theory)
-- ════════════════════════════════════════════════════════════════

/-! With the lattice bridge in place, De Morgan laws follow directly
from mathlib's `compl_inf` / `compl_sup` rather than requiring
manual proof. -/

theorem neg_conj (p q : F.Denot .t) :
    neg (conj p q) = disj (neg p) (neg q) := by
  simp only [neg, conj, disj]
  exact propext not_and_or

theorem neg_disj (p q : F.Denot .t) :
    neg (disj p q) = conj (neg p) (neg q) := by
  simp only [neg, conj, disj]
  exact propext not_or

-- ════════════════════════════════════════════════════════════════
-- § Predicate Lattice and Set-Theoretic Connections
-- ════════════════════════════════════════════════════════════════

/-! Properties (`F.Denot (.e ⇒ .t) = F.Entity → Prop`) are elements
of a complete lattice. The lattice operations correspond to
set-theoretic operations on the extensions of predicates. -/

/-- Predicate conjunction = set intersection of extensions. -/
theorem genConj_et_eq_inter (f g : F.Denot (.e ⇒ .t)) :
    predicateToSet (genConj (.e ⇒ .t) F f g) =
    predicateToSet f ∩ predicateToSet g := by
  ext x; simp [predicateToSet, genConj, Set.mem_inter_iff]

/-- Predicate disjunction = set union of extensions. -/
theorem genDisj_et_eq_union (f g : F.Denot (.e ⇒ .t)) :
    predicateToSet (genDisj (.e ⇒ .t) F f g) =
    predicateToSet f ∪ predicateToSet g := by
  ext x; simp [predicateToSet, genDisj, Set.mem_union]

-- ════════════════════════════════════════════════════════════════
-- § Truth, Validity, and Entailment (DWP Ch. 6 §2.C)
-- ════════════════════════════════════════════════════════════════

/-! Model-theoretic notions from @cite{dowty-wall-peters-1981} Def C.1.
Since we work denotationally (Lean's type system is the metalanguage),
these definitions apply to *closed* propositions — those already
evaluated under some assignment. -/

/-- A proposition is **true at index** `i` iff it holds there.
    DWP Def C.1: "φ is true with respect to M and to ⟨w, t⟩ iff
    ⟦φ⟧^{M,w,t,g} is 1 for all value assignments g." -/
def trueAt (p : F.Denot .prop) (i : F.Index) : Prop := p i

/-- A proposition is **valid** iff it is true at every index.
    Equivalently: `box p`. -/
def valid (p : F.Denot .prop) : Prop := ∀ i, p i

/-- A proposition is **satisfiable** iff it is true at some index.
    Equivalently: `diamond p`. -/
def satisfiable (p : F.Denot .prop) : Prop := ∃ i, p i

/-- Semantic entailment: `p₁, ..., pₙ ⊨ q` iff at every index where
    all premises are true, the conclusion is true. -/
def entails (premises : List (F.Denot .prop)) (q : F.Denot .prop) : Prop :=
  ∀ i, (∀ p ∈ premises, trueAt p i) → trueAt q i

theorem valid_eq_box (p : F.Denot .prop) :
    valid (F := F) p = box p := rfl

theorem satisfiable_eq_diamond (p : F.Denot .prop) :
    satisfiable (F := F) p = diamond p := rfl

/-- Validity implies truth at any particular index. -/
theorem valid_trueAt (p : F.Denot .prop) (i : F.Index)
    (h : valid (F := F) p) : trueAt p i :=
  h i

/-- A valid proposition is satisfiable (when Index is inhabited). -/
theorem valid_satisfiable [Inhabited F.Index] (p : F.Denot .prop)
    (h : valid (F := F) p) : satisfiable p :=
  ⟨default, h default⟩

/-- An unsatisfiable proposition is not valid (contrapositively). -/
theorem not_satisfiable_not_valid [Inhabited F.Index] (p : F.Denot .prop)
    (h : ¬ satisfiable (F := F) p) : ¬ valid p :=
  fun hv => h (valid_satisfiable p hv)

/-- Entailment from an empty premise set is validity. -/
theorem entails_nil (q : F.Denot .prop) :
    entails (F := F) [] q = valid q := by
  simp [entails, valid, trueAt, List.not_mem_nil]

/-- Single-premise entailment: `p ⊨ q` iff `□(p → q)`. -/
theorem entails_singleton (p q : F.Denot .prop) :
    entails (F := F) [p] q = box (fun i => impl (p i) (q i)) := by
  simp [entails, trueAt, box, impl]

end Core.IntensionalLogic.Algebra
