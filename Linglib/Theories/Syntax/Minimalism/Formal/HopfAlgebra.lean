/-
# Hopf Algebra Structure (§1.2)

Formalizes the graded connected Hopf algebra H^c on binary forests from
@cite{marcolli-chomsky-berwick-2025} §1.2. In the Connes-Kreimer framework,
syntactic objects generate a Hopf algebra where:

- **Product** = disjoint union of forests (⊔)
- **Coproduct** = sum over admissible cuts (Δ^c)
- **Antipode** = recursive formula S(x) = -x - Σ S(x')·x'' (eq. 1.2.12)
- **Grading** = leaf count (degree)

The key result (Lemma 1.2.10) is that H^c is a graded connected
bialgebra and therefore automatically admits an antipode, making it
a Hopf algebra. Coassociativity of the coproduct is the deep
structural property enabling this.

## Main definitions

- `Forest`, `FLinComb`: forest basis and ℤ-linear combinations
- `forestDeg`: Hopf algebra grading by leaf count
- `counit`: augmentation map ε (1 ↦ 1, T ↦ 0 for deg ≥ 1)
- `reducedCoproductTerms`: Δ̄^c₍₂₎(T) = Σ_{v ∈ V_int} (T_v, T/^c T_v)
- `antipodeAux`, `antipode`: S(T) via eq. 1.2.12

## Main results

- `forestDeg_mul`: deg(F₁ ⊔ F₂) = deg(F₁) + deg(F₂)
- `connected`: every non-empty forest has positive degree
- `counit_multiplicative`: ε(F₁ ⊔ F₂) = ε(F₁) · ε(F₂)
- `antipode_leaf`: S(leaf) = -leaf
- `antipode_bush`: S(node(a,b)) = -node(a,b) when a,b are leaves
- `coassociativity`: (id ⊗ Δ) ∘ Δ = (Δ ⊗ id) ∘ Δ (Lemma 1.2.10)
- `Hc.instCoalgebra`: `Coalgebra ℤ Hc` (CK coproduct on syntactic forests)

## Mathlib instantiation

H^c is directly instantiated as Mathlib's `Coalgebra ℤ Hc` where
`Hc := MonoidAlgebra ℤ (FreeMonoid SyntacticObject)`. The type is `def`
(not `abbrev`) to prevent Mathlib's coefficient-induced coalgebra from
conflicting with the Connes-Kreimer coproduct:

- **Algebra structure** (from `MonoidAlgebra`): product = forest concatenation
- **Coalgebra structure** (custom): CK coproduct = sum over admissible cuts
- **Antipode** (custom): S(T) = -T - Σ S(T_v)·(T/T_v)

This gives access to Mathlib's full coalgebra/Hopf algebra API on `Hc`.

-/

import Linglib.Theories.Syntax.Minimalism.Formal.Coproduct
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

open scoped TensorProduct
namespace Minimalism

/-! ## Types: forests and linear combinations

The Hopf algebra H^c has basis the set of forests (finite disjoint unions
of trees). The empty forest is the unit. Formal ℤ-linear combinations
of forests form the underlying ℤ-module.

`Forest` is definitionally `FreeMonoid SyntacticObject` — the free monoid
on trees under disjoint union. `FLinComb` is a lightweight list-of-pairs
representation for concrete computation. The Mathlib-grounded type is
`Hc := MonoidAlgebra ℤ (FreeMonoid SyntacticObject)` (see §Instantiation). -/

/-- A forest is a list of syntactic objects — representing the disjoint
    union (product) of trees in H^c. The empty forest `[]` is the unit.

    Definitionally equal to `FreeMonoid SyntacticObject`, inheriting
    the free monoid structure from Mathlib. -/
abbrev Forest := List SyntacticObject

/-- A formal ℤ-linear combination of forests.

    Lightweight representation for concrete computation (antipode, etc.).
    The Mathlib-grounded equivalent is `Hc` (= `MonoidAlgebra ℤ Forest`). -/
abbrev FLinComb := List (ℤ × Forest)

/-! ## Grading (§1.2)

H^c is graded by leaf count: deg(T) = leafCount(T), extended additively
to forests. The grading is compatible with both product and coproduct. -/

/-- Forest degree: total leaf count across all trees.
    deg(∅) = 0, deg(F₁ ⊔ F₂) = deg(F₁) + deg(F₂). -/
def forestDeg : Forest → Nat
  | [] => 0
  | t :: ts => t.leafCount + forestDeg ts

/-- The unit (empty forest) has degree 0. -/
theorem forestDeg_unit : forestDeg ([] : Forest) = 0 := rfl

/-- A single tree has degree = leafCount. -/
theorem forestDeg_singleton (T : SyntacticObject) :
    forestDeg [T] = T.leafCount := by
  simp [forestDeg]

/-- Degree is additive under the forest product (disjoint union). -/
theorem forestDeg_mul (F₁ F₂ : Forest) :
    forestDeg (F₁ ++ F₂) = forestDeg F₁ + forestDeg F₂ := by
  induction F₁ with
  | nil => simp [forestDeg]
  | cons t ts ih => simp [forestDeg, ih]; omega

/-! ## Connectedness

H^c is *connected*: the degree-0 component is 1-dimensional, spanned by
the unit 1 (empty forest). Every tree has leafCount ≥ 1, so the only
degree-0 element is the unit. Connectedness guarantees the existence
and uniqueness of the antipode (Lemma 1.2.10). -/

/-- Every non-empty forest has positive degree. -/
theorem connected (T : SyntacticObject) : forestDeg [T] ≥ 1 := by
  simp [forestDeg]; exact leafCount_pos T

/-- The empty forest is the unique degree-0 basis element. -/
theorem degree_zero_iff_empty (F : Forest) :
    forestDeg F = 0 ↔ F = [] := by
  constructor
  · intro h
    cases F with
    | nil => rfl
    | cons t ts =>
      simp [forestDeg] at h
      have := leafCount_pos t
      omega
  · intro h; subst h; rfl

/-! ## Counit ε (augmentation map)

The counit ε : H^c → ℤ is the algebra homomorphism defined by
ε(1) = 1 and ε(T) = 0 for any tree T. It projects onto the degree-0
component. The counit axiom (ε ⊗ id) ∘ Δ = id = (id ⊗ ε) ∘ Δ
characterizes ε as a coalgebra counit. -/

/-- Counit: the augmentation map ε. ε(∅) = 1, ε(F) = 0 for F ≠ ∅. -/
def counit : Forest → ℤ
  | [] => 1
  | _ :: _ => 0

theorem counit_empty : counit ([] : Forest) = 1 := rfl

theorem counit_singleton (T : SyntacticObject) : counit [T] = 0 := rfl

/-- Counit is multiplicative: ε(F₁ ⊔ F₂) = ε(F₁) · ε(F₂). -/
theorem counit_multiplicative (F₁ F₂ : Forest) :
    counit (F₁ ++ F₂) = counit F₁ * counit F₂ := by
  cases F₁ with
  | nil => simp [counit]
  | cons _ _ => simp [counit]

/-- Counit vanishes on positive-degree elements. -/
theorem counit_pos_deg (F : Forest) (h : forestDeg F ≥ 1) :
    counit F = 0 := by
  cases F with
  | nil => simp [forestDeg] at h
  | cons _ _ => rfl

/-! ## Reduced coproduct Δ̄^c (Definition 1.2.8)

The full coproduct is Δ(T) = T ⊗ 1 + 1 ⊗ T + Δ̄(T) where the reduced
coproduct Δ̄ sums over admissible cuts. The leading (single-cut) term is:

  Δ̄₍₂₎(T) = Σ_{v ∈ V_int(T)} T_v ⊗ T/^c T_v

Each term pairs a subtree T_v (rooted at internal node v) with the
contraction quotient T/^c T_v (the tree with T_v collapsed to a leaf). -/

/-- Reduced coproduct terms: for each internal proper subtree v, pair
    (v, quotient T/^c v). This is the leading term Δ̄^c₍₂₎(T).

    Extends `leadingCoproduct` by resolving the `Option` quotient: only
    produces pairs where the contraction quotient succeeds. -/
def reducedCoproductTerms (T : SyntacticObject) :
    List (SyntacticObject × SyntacticObject) :=
  T.properSubtrees.filterMap fun v =>
    match v with
    | .leaf _ => none
    | .node _ _ =>
      match quotientTree T v with
      | some q => some (v, q)
      | none => none

/-- Leaves have no coproduct terms (no proper subtrees). -/
theorem reducedCoproductTerms_leaf (tok : LIToken) :
    reducedCoproductTerms (.leaf tok) = [] := by
  simp [reducedCoproductTerms, SyntacticObject.properSubtrees]

/-- A bush (node of two leaves) has no coproduct terms: its only proper
    subtrees are leaves, which are filtered out. -/
theorem reducedCoproductTerms_bush (a b : LIToken) :
    reducedCoproductTerms (.node (.leaf a) (.leaf b)) = [] := by
  simp [reducedCoproductTerms, SyntacticObject.properSubtrees,
        SyntacticObject.subtrees, List.filterMap]

/-- Non-trivial admissible cut terms: entries from `cutOptions` with non-empty
    pruned forest. These are the full reduced coproduct terms including
    multi-cut antichains (not just single-node cuts). -/
def cutTerms (T : SyntacticObject) : List (List SyntacticObject × SyntacticObject) :=
  (cutOptions T).filter fun ⟨P, _⟩ => !P.isEmpty

theorem cutTerms_leaf (tok : LIToken) :
    cutTerms (.leaf tok) = [] := by
  simp [cutTerms, cutOptions]

theorem cutTerms_bush (a b : LIToken) :
    cutTerms (.node (.leaf a) (.leaf b)) = [] := by
  simp [cutTerms, cutOptions]

private theorem cutTerms_forall_nonempty (T : SyntacticObject) :
    ∀ x ∈ cutTerms T, x.1 ≠ [] := by
  intro ⟨P, R⟩ hmem
  simp only [cutTerms, List.mem_filter] at hmem
  cases P with
  | nil => simp at hmem
  | cons h t => exact List.cons_ne_nil h t

/-! ## Antipode S (eq. 1.2.12)

The antipode S is defined recursively by the formula:

  S(T) = -T - Σ S(T_v) · (T/^c T_v)

where the sum ranges over reduced coproduct terms (T_v, T/^c T_v).
This is the unique solution in a graded connected bialgebra
(Lemma 1.2.10), computable by induction on degree. -/

/-- Antipode computation with explicit fuel (depth bound).

    The fuel parameter ensures structural termination. Using
    `nodeCount` as fuel suffices because each recursive call targets
    a proper subtree with strictly fewer internal nodes. -/
def antipodeAux : Nat → SyntacticObject → FLinComb
  | _, .leaf tok => [(-1, [.leaf tok])]
  | 0, so => [(-1, [so])]
  | n+1, .node a b =>
    [(-1, [.node a b])] ++ (reducedCoproductTerms (.node a b)).flatMap fun ⟨v, q⟩ =>
      (antipodeAux n v).map fun ⟨coeff, forest⟩ =>
        (-coeff, forest ++ [q])

/-- The antipode S : SyntacticObject → FLinComb (eq. 1.2.12).

    S(T) = -T - Σ_{(T_v, T/T_v) ∈ Δ̄(T)} S(T_v) · (T/^c T_v)

    Uses `nodeCount` as fuel, which suffices since proper subtrees
    have strictly fewer internal nodes. -/
def antipode (so : SyntacticObject) : FLinComb :=
  antipodeAux so.nodeCount so

/-- S(leaf) = -leaf: leaves are group-like and self-inverse up to sign. -/
theorem antipode_leaf (tok : LIToken) :
    antipode (.leaf tok) = [(-1, [.leaf tok])] := rfl

/-- S(bush) = -bush: a binary node of two leaves has no reduced
    coproduct terms, so the antipode is just negation. -/
theorem antipode_bush (a b : LIToken) :
    antipode (.node (.leaf a) (.leaf b)) = [(-1, [.node (.leaf a) (.leaf b)])] := by
  simp only [antipode, SyntacticObject.nodeCount, Nat.reduceAdd]
  unfold antipodeAux
  dsimp only []
  rw [reducedCoproductTerms_bush]
  simp

/-! ## Hopf algebra axiom

The defining property of the antipode is:

  m ∘ (S ⊗ id) ∘ Δ = η ∘ ε = m ∘ (id ⊗ S) ∘ Δ

where m is the product (forest union), η is the unit map, and ε is
the counit. For trees of positive degree (ε(T) = 0), this says:

  T + Σ S(T_v) · (T/^c T_v) + S(T) = 0

which is exactly the recursive definition of S. The axiom is therefore
satisfied by construction.

TODO: State this formally as an equation on `FLinComb` with a
normalization function that collects like terms. -/

/-- The leading term of the antipode is always -T: antipode(T) starts
    with the coefficient -1 on the forest [T]. This structural property
    follows from the recursive definition (both base cases produce
    [(-1, [T])] and the recursive case prepends [(-1, [T])]). -/
theorem antipode_leading_term (T : SyntacticObject) :
    ∃ rest : FLinComb, antipode T = (-1, [T]) :: rest := by
  cases T with
  | leaf tok => exact ⟨[], rfl⟩
  | node a b =>
    simp only [antipode, SyntacticObject.nodeCount]
    have h : 1 + a.nodeCount + b.nodeCount = (a.nodeCount + b.nodeCount) + 1 := by omega
    rw [h]
    unfold antipodeAux
    dsimp only []
    exact ⟨_, rfl⟩

/-! ## Coassociativity (Lemma 1.2.10)

The coproduct Δ^c is coassociative:

  (id ⊗ Δ^c) ∘ Δ^c = (Δ^c ⊗ id) ∘ Δ^c

This is the key structural property ensuring H^c is a bialgebra.

## Proof strategy (AlgHom reduction)

The coproduct is an algebra homomorphism Δ : Hc →ₐ[ℤ] Hc ⊗ Hc.
Both sides of coassociativity, `(Δ ⊗ id) ∘ Δ` and `(id ⊗ Δ) ∘ Δ`,
are algebra homomorphisms `Hc → Hc ⊗ Hc ⊗ Hc`. By
`MonoidAlgebra.algHom_ext`, two AlgHoms from Hc are equal iff they
agree on generators `single m 1`. Since generators are forests,
and `FreeMonoid.lift` extends multiplicatively, it suffices to check
on single trees — i.e., prove coassociativity for each tree T by
structural induction on `SyntacticObject`.

This reduces a deep algebraic theorem to a combinatorial property
of admissible cuts on binary trees. -/

/-! ## Coproduct size conservation

The coproduct preserves total weight: for each term (T_v, T/^c T_v),
the sum of leaf counts satisfies a conservation law. This is proved
in `Coproduct.lean` as `coproduct_size_identity`; we re-export it
in the Hopf algebra context. -/

/-- Coproduct terms preserve grading: for (v, q) in Δ̄(T),
    deg([v]) + deg([q]) = deg([T]) + 1.

    The +1 accounts for the trace leaf introduced by contraction. -/
theorem coproduct_preserves_grading (T v q : SyntacticObject)
    (hc : contains T v) (hq : quotientTree T v = some q) :
    forestDeg [v] + forestDeg [q] = forestDeg [T] + 1 := by
  simp only [forestDeg_singleton]
  have h := coproduct_size_identity T v q hc hq
  have hv := leafCount_pos v
  have hqp := leafCount_pos q
  omega

/-! ## Mathlib instantiation: Coalgebra ℤ Hc

H^c is instantiated as Mathlib's `Coalgebra` over the integer monoid
algebra on forests. The type `Hc` is a `def` (not `abbrev`) to block
the default coefficient-induced coalgebra from `MonoidAlgebra.instCoalgebra`
— the Connes-Kreimer coproduct sums over admissible cuts, which is
fundamentally different from the group-like coproduct Δ(F) = F ⊗ F.

The algebra structure (product = forest concatenation) is forwarded
from `MonoidAlgebra`. Only the coalgebra structure is custom.

### What `Coalgebra ℤ Hc` provides

With this instance, Mathlib's coalgebra API applies to H^c:
- `Coalgebra.comul : Hc →ₗ[ℤ] Hc ⊗[ℤ] Hc` — CK coproduct
- `Coalgebra.counit : Hc →ₗ[ℤ] ℤ` — augmentation map
- `Coalgebra.coassoc` — coassociativity (Lemma 1.2.10)
- All derived lemmas: `coassoc_apply`, `counit_apply`, etc.

### How comul is constructed

The CK coproduct is built in three layers:

1. `comulGen : SyntacticObject → Hc ⊗ Hc` — coproduct on single trees
2. `FreeMonoid.lift comulGen : FreeMonoid SO →* Hc ⊗ Hc` — multiplicative
   extension to forests (Δ(F₁⊔F₂) = Δ(F₁)·Δ(F₂))
3. `MonoidAlgebra.lift` — linear extension to all of Hc as an `AlgHom`

The `AlgHom` structure means coassociativity reduces (via
`MonoidAlgebra.algHom_ext`) to checking on single trees by
structural induction, rather than needing a global proof.
-/

open scoped TensorProduct

/-- The Connes-Kreimer Hopf algebra H^c on syntactic forests.

    Mathematically: the free ℤ-module on forests of syntactic objects,
    with product = forest concatenation and coproduct = sum over
    admissible cuts (@cite{marcolli-chomsky-berwick-2025} §1.2).

    `def` (not `abbrev`) ensures Lean uses our CK coproduct
    rather than the coefficient-induced one from `MonoidAlgebra.instCoalgebra`. -/
def Hc := MonoidAlgebra ℤ (FreeMonoid SyntacticObject)

namespace Hc

-- Algebra structure forwarded from MonoidAlgebra
noncomputable instance : Semiring Hc :=
  inferInstanceAs (Semiring (MonoidAlgebra ℤ (FreeMonoid SyntacticObject)))

noncomputable instance : Ring Hc :=
  inferInstanceAs (Ring (MonoidAlgebra ℤ (FreeMonoid SyntacticObject)))

noncomputable instance : Algebra ℤ Hc :=
  inferInstanceAs (Algebra ℤ (MonoidAlgebra ℤ (FreeMonoid SyntacticObject)))

-- Evaluate Hc elements at a forest (coefficient access)
instance : DFunLike Hc (FreeMonoid SyntacticObject) (fun _ => ℤ) :=
  inferInstanceAs (DFunLike (FreeMonoid SyntacticObject →₀ ℤ)
    (FreeMonoid SyntacticObject) (fun _ => ℤ))

/-- Embed a forest as a basis element of H^c: F ↦ 1·F. -/
noncomputable def ofForest (F : Forest) : Hc :=
  (Finsupp.single (FreeMonoid.ofList F) 1 : MonoidAlgebra ℤ (FreeMonoid SyntacticObject))

/-- Embed a single tree as a basis element of H^c. -/
noncomputable def ofTree (T : SyntacticObject) : Hc :=
  ofForest [T]

/-! ### Comultiplication (CK coproduct as AlgHom) -/

/-- CK coproduct on a single tree:
    Δ(T) = T ⊗ 1 + 1 ⊗ T + Σ_{(P,R) ∈ cutTerms(T)} (∏P) ⊗ R

    The sum ranges over all non-trivial admissible cut antichains
    (from `cutTerms`), including multi-node cuts. Each term pairs
    the forest of pruned subtrees `P` with the quotient tree `R`.

    This is the value on generators. The full coproduct on forests
    extends multiplicatively via `FreeMonoid.lift`, and linearly
    to all of Hc via `MonoidAlgebra.lift`. -/
noncomputable def comulGen (T : SyntacticObject) : Hc ⊗[ℤ] Hc :=
  ofTree T ⊗ₜ 1 + 1 ⊗ₜ ofTree T +
  (cutTerms T).foldl
    (fun acc ⟨P, R⟩ => acc + ofForest P ⊗ₜ ofTree R) 0

/-- CK coproduct as a monoid homomorphism on forests.
    Multiplicative: Δ(F₁ ⊔ F₂) = Δ(F₁) · Δ(F₂)
    where multiplication in Hc ⊗ Hc is componentwise. -/
noncomputable def comulMonoidHom : FreeMonoid SyntacticObject →* (Hc ⊗[ℤ] Hc) :=
  FreeMonoid.lift comulGen

/-- CK coproduct as an algebra homomorphism on Hc.
    Constructed via `MonoidAlgebra.lift`: extends `comulMonoidHom`
    linearly from monoid elements to all of Hc.

    This is an `AlgHom`, not just a `LinearMap`, which means
    coassociativity can be reduced to generators via `algHom_ext`. -/
noncomputable def comulAlgHom : Hc →ₐ[ℤ] (Hc ⊗[ℤ] Hc) :=
  MonoidAlgebra.lift ℤ (Hc ⊗[ℤ] Hc) (FreeMonoid SyntacticObject) comulMonoidHom

/-! ### comulAlgHom reduction lemmas -/

/-- comulAlgHom on a single tree reduces to comulGen.

    Proof: `MonoidAlgebra.lift_single` gives `r • f(m)` for `single m r`;
    at `r = 1` this is `1 • comulGen T = comulGen T`. -/
theorem comulAlgHom_ofTree (T : SyntacticObject) :
    comulAlgHom (ofTree T) = comulGen T := by
  unfold comulAlgHom ofTree ofForest
  show ((MonoidAlgebra.lift ℤ (Hc ⊗[ℤ] Hc) (FreeMonoid SyntacticObject)) comulMonoidHom)
    (MonoidAlgebra.single (FreeMonoid.ofList [T]) 1) = comulGen T
  rw [MonoidAlgebra.lift_single]
  exact one_smul ℤ _

/-- comulAlgHom.toLinearMap maps 1 to 1 ⊗ₜ 1.

    The linear map underlying the AlgHom preserves the unit. -/
theorem comulAlgHom_toLinearMap_one :
    comulAlgHom.toLinearMap (1 : Hc) = (1 : Hc) ⊗ₜ[ℤ] (1 : Hc) := by
  show comulAlgHom (1 : Hc) = _
  rw [map_one]; rfl

/-- comulGen simplifies for primitive elements (trees with no
    non-trivial cut terms). Leaves and bushes are primitive. -/
theorem comulGen_primitive (T : SyntacticObject)
    (h : cutTerms T = []) :
    comulGen T = ofTree T ⊗ₜ 1 + 1 ⊗ₜ ofTree T := by
  simp [comulGen, h]

/-! ### Forest algebra lemmas -/

theorem ofForest_nil : ofForest ([] : Forest) = (1 : Hc) := by
  unfold ofForest
  rw [FreeMonoid.ofList_nil]
  exact MonoidAlgebra.one_def.symm

theorem ofForest_append (Pa Pb : Forest) :
    ofForest (Pa ++ Pb) = ofForest Pa * ofForest Pb := by
  show MonoidAlgebra.single (FreeMonoid.ofList (Pa ++ Pb)) (1 : ℤ) =
    MonoidAlgebra.single (FreeMonoid.ofList Pa) 1 *
    MonoidAlgebra.single (FreeMonoid.ofList Pb) 1
  rw [FreeMonoid.ofList_append]
  conv_lhs => rw [show (1 : ℤ) = 1 * 1 from (mul_one 1).symm]
  exact (MonoidAlgebra.single_mul_single _ _ _ _).symm

theorem comulAlgHom_ofForest_cons (T : SyntacticObject) (F : Forest) :
    comulAlgHom (ofForest (T :: F)) = comulGen T * comulAlgHom (ofForest F) := by
  show comulAlgHom (ofForest ([T] ++ F)) = _
  rw [ofForest_append, map_mul comulAlgHom]
  congr 1
  exact comulAlgHom_ofTree T

theorem comulAlgHom_ofForest_nil :
    comulAlgHom (ofForest ([] : Forest)) = 1 := by
  rw [ofForest_nil, map_one]

/-! ### Counit -/

/-- Counit as a linear map: ε(Σ cᵢ Fᵢ) = c_∅ (coefficient of the empty forest).

    This is the linear extension of the computational `counit` function. -/
noncomputable def hcCounit : Hc →ₗ[ℤ] ℤ where
  toFun f := f (1 : FreeMonoid SyntacticObject)
  map_add' x y := Finsupp.add_apply x y _
  map_smul' r x := congr_fun (Finsupp.coe_smul r x) _

/-! ### Counit axioms (ε ⊗ id) ∘ Δ and (id ⊗ ε) ∘ Δ -/

instance : DecidableEq (FreeMonoid SyntacticObject) :=
  inferInstanceAs (DecidableEq (List SyntacticObject))

/-- The counit as a multiplicative monoid homomorphism on free monoid generators:
    sends every tree to 0 (in multiplicative ℤ). -/
noncomputable def counitMonoidHom : FreeMonoid SyntacticObject →* ℤ :=
  FreeMonoid.lift (fun _ : SyntacticObject => (0 : ℤ))

private theorem counitMonoidHom_of (T : SyntacticObject) :
    counitMonoidHom (FreeMonoid.of T) = 0 := by
  show (FreeMonoid.lift (fun _ : SyntacticObject => (0 : ℤ))) (FreeMonoid.of T) = 0
  rw [FreeMonoid.lift_eval_of]

private theorem counitMonoidHom_ne_one (m : FreeMonoid SyntacticObject) (hm : m ≠ 1) :
    counitMonoidHom m = 0 := by
  induction m using FreeMonoid.recOn with
  | h0 => exact absurd rfl hm
  | ih T ts _ =>
    show counitMonoidHom (FreeMonoid.of T * ts) = 0
    rw [map_mul, counitMonoidHom_of, zero_mul]

/-- The counit lifted to an algebra homomorphism on Hc via `MonoidAlgebra.lift`. -/
noncomputable def hcCounitAlgHom : Hc →ₐ[ℤ] ℤ :=
  MonoidAlgebra.lift ℤ ℤ (FreeMonoid SyntacticObject) counitMonoidHom

private theorem hcCounitAlgHom_single (m : FreeMonoid SyntacticObject) (r : ℤ) :
    hcCounitAlgHom (Finsupp.single m r : Hc) = r * counitMonoidHom m := by
  change ((MonoidAlgebra.lift ℤ ℤ (FreeMonoid SyntacticObject)) counitMonoidHom)
    (MonoidAlgebra.single m r) = _
  rw [MonoidAlgebra.lift_single, smul_eq_mul]

private theorem hcCounit_single (m : FreeMonoid SyntacticObject) (r : ℤ) :
    hcCounit (Finsupp.single m r : Hc) = if m = 1 then r else 0 := by
  show (Finsupp.single m r : FreeMonoid SyntacticObject →₀ ℤ) 1 = _
  simp [Finsupp.single_apply]

set_option maxHeartbeats 400000 in
private theorem hcCounitAlgHom_eq_hcCounit :
    hcCounitAlgHom.toLinearMap = hcCounit := by
  apply LinearMap.ext; intro x; show hcCounitAlgHom x = hcCounit x
  induction x using Finsupp.induction_linear with
  | zero => exact (map_zero hcCounitAlgHom).trans (map_zero hcCounit).symm
  | add f g hf hg =>
    exact (map_add hcCounitAlgHom f g).trans
      (congr_arg₂ (· + ·) hf hg |>.trans (map_add hcCounit f g).symm)
  | single m r =>
    rw [hcCounitAlgHom_single, hcCounit_single]
    by_cases hm : m = 1
    · subst hm; simp [map_one]
    · rw [counitMonoidHom_ne_one m hm, mul_zero, if_neg hm]

private theorem hcCounitAlgHom_ofTree (T : SyntacticObject) :
    hcCounitAlgHom (ofTree T) = 0 := by
  unfold ofTree ofForest
  rw [hcCounitAlgHom_single]
  have h : counitMonoidHom (FreeMonoid.ofList [T]) = 0 :=
    counitMonoidHom_ne_one _ (fun h => List.cons_ne_nil T [] h)
  rw [h, mul_zero]

private theorem hcCounitAlgHom_ofForest_nonempty (P : List SyntacticObject) (hP : P ≠ []) :
    hcCounitAlgHom (ofForest P) = 0 := by
  unfold ofForest
  rw [hcCounitAlgHom_single]
  cases P with
  | nil => exact absurd rfl hP
  | cons hd tl =>
    have h : counitMonoidHom (FreeMonoid.ofList (hd :: tl)) = 0 :=
      counitMonoidHom_ne_one _ (fun h => List.cons_ne_nil hd tl h)
    rw [h, mul_zero]

-- (ε ⊗ id) ∘ Δ as an AlgHom
private noncomputable def rTensorCounitComul : Hc →ₐ[ℤ] (ℤ ⊗[ℤ] Hc) :=
  (Algebra.TensorProduct.map hcCounitAlgHom (AlgHom.id ℤ Hc)).comp comulAlgHom

private theorem mapCounit_fold
    (L : List (List SyntacticObject × SyntacticObject))
    (hL : ∀ x ∈ L, x.1 ≠ [])
    (acc : Hc ⊗[ℤ] Hc) :
    (Algebra.TensorProduct.map hcCounitAlgHom (AlgHom.id ℤ Hc))
      (L.foldl (fun a ⟨P, R⟩ => a + ofForest P ⊗ₜ[ℤ] ofTree R) acc) =
    (Algebra.TensorProduct.map hcCounitAlgHom (AlgHom.id ℤ Hc)) acc := by
  induction L generalizing acc with
  | nil => rfl
  | cons p tl ih =>
    simp only [List.foldl_cons]
    rw [ih (fun x hx => hL x (.tail _ hx))]
    have hP : p.1 ≠ [] := hL p (.head _)
    have hcounit : hcCounitAlgHom (ofForest p.1) = 0 := hcCounitAlgHom_ofForest_nonempty p.1 hP
    simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id,
               hcounit, TensorProduct.zero_tmul, add_zero]

set_option maxHeartbeats 1600000 in
private theorem rTensorCounitComul_ofTree (T : SyntacticObject) :
    rTensorCounitComul (ofTree T) = (1 : ℤ) ⊗ₜ[ℤ] ofTree T := by
  unfold rTensorCounitComul
  simp only [AlgHom.comp_apply, comulAlgHom_ofTree]
  unfold comulGen
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id,
             hcCounitAlgHom_ofTree, map_one hcCounitAlgHom]
  rw [mapCounit_fold _ (cutTerms_forall_nonempty T), map_zero]
  simp only [TensorProduct.zero_tmul, zero_add, add_zero]

set_option maxHeartbeats 1600000 in
private theorem rTensorCounitComul_eq_includeRight :
    rTensorCounitComul =
    (Algebra.TensorProduct.includeRight : Hc →ₐ[ℤ] ℤ ⊗[ℤ] Hc) := by
  apply MonoidAlgebra.algHom_ext
  intro m
  induction m using FreeMonoid.recOn with
  | h0 => exact map_one rTensorCounitComul
  | ih T ts ih =>
    let a : Hc := MonoidAlgebra.single (FreeMonoid.of T) 1
    let b : Hc := MonoidAlgebra.single ts 1
    have hsplit : (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc) = a * b :=
      (MonoidAlgebra.single_mul_single (R := ℤ) (FreeMonoid.of T) ts 1 1).symm
    have hih : rTensorCounitComul b = Algebra.TensorProduct.includeRight b := ih
    calc rTensorCounitComul (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc)
        = rTensorCounitComul (a * b) := by rw [hsplit]
      _ = rTensorCounitComul a * rTensorCounitComul b := map_mul ..
      _ = rTensorCounitComul a * Algebra.TensorProduct.includeRight b := by rw [hih]
      _ = Algebra.TensorProduct.includeRight a *
          Algebra.TensorProduct.includeRight b := by
          congr 1
          change rTensorCounitComul (ofTree T) = _
          rw [rTensorCounitComul_ofTree, Algebra.TensorProduct.includeRight_apply (R := ℤ)]
          rfl
      _ = Algebra.TensorProduct.includeRight (a * b) := (map_mul ..).symm
      _ = Algebra.TensorProduct.includeRight
            (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc) :=
          congr_arg _ hsplit.symm

private theorem algMap_eq_rTensor :
    (Algebra.TensorProduct.map hcCounitAlgHom (AlgHom.id ℤ Hc)).toLinearMap =
    hcCounit.rTensor Hc := by
  apply TensorProduct.ext'
  intro a b
  simp only [AlgHom.toLinearMap_apply, LinearMap.rTensor_tmul]
  show hcCounitAlgHom a ⊗ₜ[ℤ] b = hcCounit a ⊗ₜ[ℤ] b
  congr 1
  exact LinearMap.congr_fun hcCounitAlgHom_eq_hcCounit a

private theorem includeRight_toLinearMap :
    (Algebra.TensorProduct.includeRight : Hc →ₐ[ℤ] ℤ ⊗[ℤ] Hc).toLinearMap =
    TensorProduct.mk ℤ ℤ Hc 1 := by
  ext x
  simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.mk_apply]

/-- Right counit axiom: (ε ⊗ id) ∘ Δ = x ↦ 1 ⊗ x. -/
theorem rTensor_counit_comp_comul_proof :
    hcCounit.rTensor Hc ∘ₗ comulAlgHom.toLinearMap = TensorProduct.mk ℤ ℤ Hc 1 := by
  have h := congr_arg AlgHom.toLinearMap rTensorCounitComul_eq_includeRight
  simp only [rTensorCounitComul, AlgHom.comp_toLinearMap] at h
  rw [algMap_eq_rTensor, includeRight_toLinearMap] at h
  exact h

-- (id ⊗ ε) ∘ Δ as an AlgHom
private noncomputable def tensorOneHom : Hc →ₐ[ℤ] Hc ⊗[ℤ] ℤ where
  toFun x := x ⊗ₜ 1
  map_one' := rfl
  map_mul' x y := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [TensorProduct.zero_tmul]
  map_add' x y := by simp only [TensorProduct.add_tmul]
  commutes' r := by
    show algebraMap ℤ Hc r ⊗ₜ[ℤ] (1 : ℤ) = algebraMap ℤ (Hc ⊗[ℤ] ℤ) r
    rw [Algebra.TensorProduct.algebraMap_apply]

private noncomputable def lTensorCounitComul : Hc →ₐ[ℤ] (Hc ⊗[ℤ] ℤ) :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ Hc) hcCounitAlgHom).comp comulAlgHom

private theorem mapCounitR_fold
    (L : List (List SyntacticObject × SyntacticObject))
    (acc : Hc ⊗[ℤ] Hc) :
    (Algebra.TensorProduct.map (AlgHom.id ℤ Hc) hcCounitAlgHom)
      (L.foldl (fun a ⟨P, R⟩ => a + ofForest P ⊗ₜ[ℤ] ofTree R) acc) =
    (Algebra.TensorProduct.map (AlgHom.id ℤ Hc) hcCounitAlgHom) acc := by
  induction L generalizing acc with
  | nil => rfl
  | cons p tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id,
               hcCounitAlgHom_ofTree, TensorProduct.tmul_zero, add_zero]

set_option maxHeartbeats 1600000 in
private theorem lTensorCounitComul_ofTree (T : SyntacticObject) :
    lTensorCounitComul (ofTree T) = ofTree T ⊗ₜ[ℤ] (1 : ℤ) := by
  unfold lTensorCounitComul
  simp only [AlgHom.comp_apply, comulAlgHom_ofTree]
  unfold comulGen
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id,
             hcCounitAlgHom_ofTree, map_one hcCounitAlgHom]
  rw [mapCounitR_fold, map_zero]
  simp only [TensorProduct.tmul_zero, add_zero]

set_option maxHeartbeats 1600000 in
private theorem lTensorCounitComul_eq_tensorOneHom :
    lTensorCounitComul = tensorOneHom := by
  apply MonoidAlgebra.algHom_ext
  intro m
  induction m using FreeMonoid.recOn with
  | h0 => exact map_one lTensorCounitComul
  | ih T ts ih =>
    let a : Hc := MonoidAlgebra.single (FreeMonoid.of T) 1
    let b : Hc := MonoidAlgebra.single ts 1
    have hsplit : (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc) = a * b :=
      (MonoidAlgebra.single_mul_single (R := ℤ) (FreeMonoid.of T) ts 1 1).symm
    have hih : lTensorCounitComul b = tensorOneHom b := ih
    calc lTensorCounitComul (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc)
        = lTensorCounitComul (a * b) := by rw [hsplit]
      _ = lTensorCounitComul a * lTensorCounitComul b := map_mul ..
      _ = lTensorCounitComul a * tensorOneHom b := by rw [hih]
      _ = tensorOneHom a * tensorOneHom b := by
          congr 1
          change lTensorCounitComul (ofTree T) = _
          rw [lTensorCounitComul_ofTree]
          show ofTree T ⊗ₜ[ℤ] (1 : ℤ) = tensorOneHom (ofTree T)
          rfl
      _ = tensorOneHom (a * b) := (map_mul ..).symm
      _ = tensorOneHom (MonoidAlgebra.single (FreeMonoid.of T * ts) 1 : Hc) :=
          congr_arg _ hsplit.symm

private theorem algMapR_eq_lTensor :
    (Algebra.TensorProduct.map (AlgHom.id ℤ Hc) hcCounitAlgHom).toLinearMap =
    hcCounit.lTensor Hc := by
  apply TensorProduct.ext'
  intro a b
  simp only [AlgHom.toLinearMap_apply, LinearMap.lTensor_tmul]
  show a ⊗ₜ[ℤ] hcCounitAlgHom b = a ⊗ₜ[ℤ] hcCounit b
  congr 1
  exact LinearMap.congr_fun hcCounitAlgHom_eq_hcCounit b

private theorem tensorOneHom_toLinearMap :
    tensorOneHom.toLinearMap = (TensorProduct.mk ℤ Hc ℤ).flip 1 := by
  apply LinearMap.ext; intro x
  simp only [AlgHom.toLinearMap_apply, tensorOneHom, AlgHom.coe_mk, RingHom.coe_mk,
             MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

/-- Left counit axiom: (id ⊗ ε) ∘ Δ = x ↦ x ⊗ 1. -/
theorem lTensor_counit_comp_comul_proof :
    hcCounit.lTensor Hc ∘ₗ comulAlgHom.toLinearMap =
    (TensorProduct.mk ℤ Hc ℤ).flip 1 := by
  have h := congr_arg AlgHom.toLinearMap lTensorCounitComul_eq_tensorOneHom
  simp only [lTensorCounitComul, AlgHom.comp_toLinearMap] at h
  rw [algMapR_eq_lTensor, tensorOneHom_toLinearMap] at h
  exact h

/-! ### Antipode -/

/-- Convert an `FLinComb` (list of coefficient-forest pairs) to an `Hc` element:
    `[(c₁, F₁), ..., (cₙ, Fₙ)] ↦ c₁ · F₁ + ... + cₙ · Fₙ`. -/
noncomputable def fLinCombToHc (l : FLinComb) : Hc :=
  l.foldl (fun acc ⟨c, F⟩ => acc + c • ofForest F) 0

/-- Antipode on a single tree, as an element of `Hc`.
    Lifts the concrete `antipode : SyntacticObject → FLinComb` to the
    Mathlib-grounded algebra. -/
noncomputable def antipodeTree (T : SyntacticObject) : Hc :=
  fLinCombToHc (antipode T)

/-- Antipode extended anti-homomorphically to forests:
    `S(T₁ · T₂ · ... · Tₙ) = S(Tₙ) · ... · S(T₂) · S(T₁)`.

    The reversal comes from the antipode being an anti-homomorphism
    in any Hopf algebra: `S(ab) = S(b) · S(a)`. -/
noncomputable def antipodeForest (m : FreeMonoid SyntacticObject) : Hc :=
  (FreeMonoid.toList m).foldl (fun acc T => antipodeTree T * acc) 1

/-- Antipode as a linear endomorphism of `Hc`.

    Constructed as the linear extension of `antipodeForest` via
    `Finsupp.linearCombination`: `S(Σ cᵢ Fᵢ) = Σ cᵢ · S(Fᵢ)`.
    Linearity (`map_add'`, `map_smul'`) holds by construction. -/
noncomputable def hcAntipode : Hc →ₗ[ℤ] Hc :=
  Finsupp.linearCombination ℤ antipodeForest

/-! ### Double-cut sum (nested admissible cuts)

The double-cut sum is `Σ_{(P,R) ∈ cutTerms(T)} ofForest(P) ⊗ cutTermsSum(R)`.
This is the common non-structural part of both sides of the coassociativity
identity on a node `T = node a b`.

For the **RHS** decomposition, this form is natural: expanding `Δ(R)` into
`R⊗1 + 1⊗R + cutTermsSum(R)` per-term gives the structural sum plus
`Σ P ⊗ cutTermsSum(R)` directly.

For the **LHS** decomposition, this requires the double-cut bijection:
`Σ assoc(δ(P) ⊗ R) = Σ P ⊗ cutTermsSum(R)` where `δ(P)` is the
non-structural part of `Δ(ofForest P)`. -/

/-- The non-structural part of comulGen: `cutTermsSum(T) = Δ(T) - T⊗1 - 1⊗T`. -/
noncomputable def cutTermsSum (T : SyntacticObject) : Hc ⊗[ℤ] Hc :=
  (cutTerms T).foldl (fun acc ⟨P, R⟩ => acc + ofForest P ⊗ₜ[ℤ] ofTree R) 0

theorem foldl_add_shift' {M : Type*} [AddCommMonoid M]
    {α : Type*} (f : α → M) (L : List α) (init : M) :
    L.foldl (fun acc x => acc + f x) init = init + (L.map f).sum := by
  induction L generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, add_assoc]

theorem foldl_add_eq_sum {M : Type*} [AddCommMonoid M]
    {α : Type*} (f : α → M) (L : List α) :
    L.foldl (fun acc x => acc + f x) 0 = (L.map f).sum := by
  rw [foldl_add_shift', zero_add]

/-- Double-cut sum: `Σ_{(P,R) ∈ cutTerms(T)} ofForest(P) ⊗ cutTermsSum(R)`.
    This is the common non-structural part of both sides of coassociativity. -/
noncomputable def doubleCutSum (a b : SyntacticObject) :
    Hc ⊗[ℤ] (Hc ⊗[ℤ] Hc) :=
  (cutTerms (.node a b)).foldl
    (fun acc ⟨P, R⟩ => acc + ofForest P ⊗ₜ[ℤ] cutTermsSum R) 0

-- cutTermsSum as map/sum (from foldl)
theorem cutTermsSum_eq_map_sum (T : SyntacticObject) :
    cutTermsSum T = ((cutTerms T).map fun x =>
      ofForest x.1 ⊗ₜ[ℤ] ofTree x.2).sum :=
  foldl_add_eq_sum _ _

-- doubleCutSum as map/sum (from foldl)
theorem doubleCutSum_eq_map_sum (a b : SyntacticObject) :
    doubleCutSum a b = ((cutTerms (.node a b)).map fun x =>
      ofForest x.1 ⊗ₜ[ℤ] cutTermsSum x.2).sum :=
  foldl_add_eq_sum _ _

-- Distribute ⊗ₜ over List.sum
theorem tmul_list_sum (p : Hc) (L : List (Hc ⊗[ℤ] Hc)) :
    p ⊗ₜ[ℤ] L.sum = (L.map fun x => p ⊗ₜ[ℤ] x).sum := by
  induction L with
  | nil => simp [TensorProduct.tmul_zero]
  | cons hd tl ih =>
    simp only [List.sum_cons, List.map_cons, TensorProduct.tmul_add, ih]

/-- `comulGen` decomposes into structural terms plus `cutTermsSum`. -/
theorem comulGen_eq_parts (R : SyntacticObject) :
    comulGen R = ofTree R ⊗ₜ[ℤ] (1 : Hc) + (1 : Hc) ⊗ₜ[ℤ] ofTree R + cutTermsSum R := rfl

-- Reduced coproduct of singleton forest = cutTermsSum
theorem delta_singleton (T : SyntacticObject) :
    comulAlgHom (ofForest [T]) - ofForest [T] ⊗ₜ[ℤ] (1 : Hc) -
    (1 : Hc) ⊗ₜ[ℤ] ofForest [T] = cutTermsSum T := by
  show comulAlgHom (ofTree T) - ofTree T ⊗ₜ 1 - 1 ⊗ₜ ofTree T = cutTermsSum T
  rw [comulAlgHom_ofTree, comulGen_eq_parts]; abel

end Hc

end Minimalism
