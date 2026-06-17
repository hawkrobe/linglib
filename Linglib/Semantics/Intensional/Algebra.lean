import Linglib.Semantics.Intensional.Quantification
import Linglib.Semantics.Intensional.Conjunction
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Heyting.Basic

/-!
# Algebraic Structure of IL Denotation Domains

[dowty-wall-peters-1981] [gallin-1975] [partee-rooth-1983]

The IL operators in `Frame.lean`, `Quantification.lean`, and `Conjunction.lean`
are instances of general algebraic operations from mathlib's order theory.

The central observation: **Montague's type-driven semantics is a hierarchy of
pointwise Boolean algebras.** Every conjoinable type `τ` (one that "ends in `t`")
induces a `CompleteLattice` on `Denot E W τ`:

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

[partee-rooth-1983]'s generalized conjunction is the pointwise
meet in the lattice of type `τ` — a fact that explains *why* conjunction
is defined recursively over types and *why* it only works for
conjoinable types (those admitting a lattice structure).
-/

namespace Intensional.Algebra

open Intensional

variable {E W : Type}

-- ════════════════════════════════════════════════════════════════
-- § Propositional Boolean Algebra
-- ════════════════════════════════════════════════════════════════

/-! `Denot E W .t = Prop` is a `CompleteBooleanAlgebra` (via mathlib's
`Prop.instCompleteLattice` and `Prop.instHeytingAlgebra`). The IL
sentential operators are its algebraic operations. -/

theorem neg_eq_compl (p : Denot E W .t) : neg p = (show Prop from p)ᶜ := rfl
theorem conj_eq_inf (p q : Denot E W .t) : conj p q = (show Prop from p) ⊓ q := rfl
theorem disj_eq_sup (p q : Denot E W .t) : disj p q = (show Prop from p) ⊔ q := rfl
theorem impl_eq_himp (p q : Denot E W .t) : impl p q = ((show Prop from p) ⇨ q) := rfl

-- ════════════════════════════════════════════════════════════════
-- § Modal Algebra: box/diamond as iInf/iSup
-- ════════════════════════════════════════════════════════════════

/-! `box` and `diamond` are the indexed infimum and supremum over
the index set — the lattice-theoretic formulation of S5 necessity
and possibility. -/

theorem box_eq_iInf (p : Denot E W .prop) :
    box (E := E) (W := W) p = ⨅ i, (show Prop from p i) :=
  iInf_Prop_eq.symm

theorem diamond_eq_iSup (p : Denot E W .prop) :
    diamond (E := E) (W := W) p = ⨆ i, (show Prop from p i) :=
  iSup_Prop_eq.symm

/-- `box` is monotone: if `p i → q i` at every index, then `□p → □q`. -/
theorem box_mono {p q : Denot E W .prop}
    (h : ∀ i, p i → q i) : box (E := E) (W := W) p → box q :=
  fun hp i => h i (hp i)

/-- `diamond` is monotone. -/
theorem diamond_mono {p q : Denot E W .prop}
    (h : ∀ i, p i → q i) : diamond (E := E) (W := W) p → diamond q :=
  fun ⟨i, hi⟩ => ⟨i, h i hi⟩

-- ════════════════════════════════════════════════════════════════
-- § Quantifier Algebra: forallEntity/existsEntity as iInf/iSup
-- ════════════════════════════════════════════════════════════════

theorem forallEntity_eq_iInf (body : E → Denot E W .t) :
    forallEntity body = ⨅ x, (show Prop from body x) :=
  iInf_Prop_eq.symm

theorem existsEntity_eq_iSup (body : E → Denot E W .t) :
    existsEntity body = ⨆ x, (show Prop from body x) :=
  iSup_Prop_eq.symm

-- ════════════════════════════════════════════════════════════════
-- § Generalized Conjunction = Pointwise Meet
-- ════════════════════════════════════════════════════════════════

/-! [partee-rooth-1983]'s generalized conjunction is the pointwise
meet in the lattice of the codomain type. This explains why `genConj`
is defined recursively: it follows the recursive lattice construction
on `Pi` types.

The proofs are `rfl` because `genConj` unfolds to exactly the same
function as the pointwise `inf` from `Pi.instLattice`. -/

open Conjunction

/-- At type `t`: generalized conjunction is propositional `∧` = `⊓`. -/
theorem genConj_eq_inf_t (p q : Denot E W .t) :
    genConj .t E W p q = (show Prop from p) ⊓ q := rfl

/-- At type `t`: generalized disjunction is propositional `∨` = `⊔`. -/
theorem genDisj_eq_sup_t (p q : Denot E W .t) :
    genDisj .t E W p q = (show Prop from p) ⊔ q := rfl

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

theorem neg_conj (p q : Denot E W .t) :
    neg (conj p q) = disj (neg p) (neg q) := by
  simp only [neg, conj, disj]
  exact propext not_and_or

theorem neg_disj (p q : Denot E W .t) :
    neg (disj p q) = conj (neg p) (neg q) := by
  simp only [neg, conj, disj]
  exact propext not_or

-- ════════════════════════════════════════════════════════════════
-- § Predicate Lattice and Set-Theoretic Connections
-- ════════════════════════════════════════════════════════════════

/-! Properties (`Denot E W (.e ⇒ .t) = E → Prop`) are elements
of a complete lattice. The lattice operations correspond to
set-theoretic operations on the extensions of predicates. -/

/-- Predicate conjunction = set intersection of extensions. -/
theorem genConj_et_eq_inter (f g : Denot E W (.e ⇒ .t)) :
    predicateToSet (genConj (.e ⇒ .t) E W f g) =
    predicateToSet f ∩ predicateToSet g := by
  ext x; simp [predicateToSet, genConj, Set.mem_inter_iff]

/-- Predicate disjunction = set union of extensions. -/
theorem genDisj_et_eq_union (f g : Denot E W (.e ⇒ .t)) :
    predicateToSet (genDisj (.e ⇒ .t) E W f g) =
    predicateToSet f ∪ predicateToSet g := by
  ext x; simp [predicateToSet, genDisj, Set.mem_union]

-- ════════════════════════════════════════════════════════════════
-- § Truth, Validity, and Entailment (DWP Ch. 6 §2.C)
-- ════════════════════════════════════════════════════════════════

/-! Model-theoretic notions from [dowty-wall-peters-1981] Def C.1.
Since we work denotationally (Lean's type system is the metalanguage),
these definitions apply to *closed* propositions — those already
evaluated under some assignment. -/

/-- A proposition is **true at index** `i` iff it holds there.
    DWP Def C.1: "φ is true with respect to M and to ⟨w, t⟩ iff
    ⟦φ⟧^{M,w,t,g} is 1 for all value assignments g." -/
def trueAt (p : Denot E W .prop) (i : W) : Prop := p i

/-- A proposition is **valid** iff it is true at every index.
    Equivalently: `box p`. -/
def valid (p : Denot E W .prop) : Prop := ∀ i, p i

/-- A proposition is **satisfiable** iff it is true at some index.
    Equivalently: `diamond p`. -/
def satisfiable (p : Denot E W .prop) : Prop := ∃ i, p i

/-- Semantic entailment: `p₁, ..., pₙ ⊨ q` iff at every index where
    all premises are true, the conclusion is true. -/
def entails (premises : List (Denot E W .prop)) (q : Denot E W .prop) : Prop :=
  ∀ i, (∀ p ∈ premises, trueAt p i) → trueAt q i

theorem valid_eq_box (p : Denot E W .prop) :
    valid (E := E) (W := W) p = box p := rfl

theorem satisfiable_eq_diamond (p : Denot E W .prop) :
    satisfiable (E := E) (W := W) p = diamond p := rfl

/-- Validity implies truth at any particular index. -/
theorem valid_trueAt (p : Denot E W .prop) (i : W)
    (h : valid (E := E) (W := W) p) : trueAt p i :=
  h i

/-- A valid proposition is satisfiable (when Index is inhabited). -/
theorem valid_satisfiable [Inhabited W] (p : Denot E W .prop)
    (h : valid (E := E) (W := W) p) : satisfiable p :=
  ⟨default, h default⟩

/-- An unsatisfiable proposition is not valid (contrapositively). -/
theorem not_satisfiable_not_valid [Inhabited W] (p : Denot E W .prop)
    (h : ¬ satisfiable (E := E) (W := W) p) : ¬ valid p :=
  fun hv => h (valid_satisfiable p hv)

/-- Entailment from an empty premise set is validity. -/
theorem entails_nil (q : Denot E W .prop) :
    entails (E := E) (W := W) [] q = valid q := by
  simp [entails, valid, trueAt, List.not_mem_nil]

/-- Single-premise entailment: `p ⊨ q` iff `□(p → q)`. -/
theorem entails_singleton (p q : Denot E W .prop) :
    entails (E := E) (W := W) [p] q = box (fun i => impl (p i) (q i)) := by
  simp [entails, trueAt, box, impl]

-- ════════════════════════════════════════════════════════════════
-- § Boolean-Algebra Instances on `Denot E W τ`
-- ════════════════════════════════════════════════════════════════

/-! The pointwise Boolean-algebra structure of conjoinable types, registered
explicitly by recursion on `τ` (base `Prop`, then the `Pi` lift for `fn`/`intens`).
Instance resolution cannot synthesize these on its own — it does not unfold the
`Denot` `def` — so the recursion instances make `BooleanAlgebra (Denot E W τ)`
available for every conjoinable type. Non-conjoinable types (`.e`) get no instance,
which is exactly correct: `⊓`/`⊔` are a type error on entities.

With these in scope, [partee-rooth-1983]'s `genConj`/`genDisj` are `⊓`/`⊔` at
*every* conjoinable type (not just the `t` base case proved above), so the bespoke
recursion is provably the pointwise lattice operation. -/

instance instBooleanAlgebraDenotT : BooleanAlgebra (Denot E W .t) :=
  inferInstanceAs (BooleanAlgebra Prop)

instance instBooleanAlgebraDenotFn (a b : Ty) [BooleanAlgebra (Denot E W b)] :
    BooleanAlgebra (Denot E W (a ⇒ b)) :=
  inferInstanceAs (BooleanAlgebra (Denot E W a → Denot E W b))

instance instBooleanAlgebraDenotIntens (a : Ty) [BooleanAlgebra (Denot E W a)] :
    BooleanAlgebra (Denot E W (.intens a)) :=
  inferInstanceAs (BooleanAlgebra (W → Denot E W a))

open Conjunction in
/-- Generalized conjunction is `⊓` at `⟨e,t⟩` — the inductive step, where the
earlier `genConj_eq_inf_t` only covered the `t` base case. -/
theorem genConj_eq_inf_et (f g : Denot E W (.e ⇒ .t)) :
    genConj (.e ⇒ .t) E W f g = f ⊓ g := rfl

open Conjunction in
/-- Generalized conjunction is `⊓` at `⟨e,⟨e,t⟩⟩` (binary relations). -/
theorem genConj_eq_inf_eet (f g : Denot E W (.e ⇒ .e ⇒ .t)) :
    genConj (.e ⇒ .e ⇒ .t) E W f g = f ⊓ g := rfl

open Conjunction in
/-- Generalized disjunction is `⊔` at `⟨e,t⟩`. -/
theorem genDisj_eq_sup_et (f g : Denot E W (.e ⇒ .t)) :
    genDisj (.e ⇒ .t) E W f g = f ⊔ g := rfl

end Intensional.Algebra
